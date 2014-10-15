open Utils

(** The language *)
type var = string
and lam = var list * exp
and exp =
  | Var of var
  | Int of int
  | Bool of bool
  | App of exp * exp list
  | Abs of lam
  | Letrec of var * exp * exp
  | If of exp * exp * exp

let rec string_of_exp = function
  | Var x -> x
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | App (f, args) ->
    Printf.sprintf "(%s %s)" (string_of_exp f)
      (String.concat " " (List.map string_of_exp args))
  | Abs (args, e) ->
    Printf.sprintf "(lambda (%s) %s)" (String.concat " " args)
      (string_of_exp e)
  | Letrec (x, e, body) ->
    Printf.sprintf "(letrec ((%s %s)) %s)" x (string_of_exp e)
      (string_of_exp body)
  | If (cond, cons, alt) ->
    Printf.sprintf "(if %s %s %s)"
      (string_of_exp cond) (string_of_exp cons) (string_of_exp alt)

let parse s =
  let rec aux (x : CCSexp.t) = match x with
    | `Atom "#t" -> Bool true
    | `Atom "#f" -> Bool false
    | `Atom x -> begin try Int (int_of_string x) with
        | Failure "int_of_string" -> Var x
      end
    | `List [`Atom "lambda"; `List args; body] ->
      Abs (List.map (function
          | `Atom v -> v
          | e -> failwith ("invalid argument: " ^ (CCSexp.to_string e)))
          args, aux body)
    | `List [`Atom "letrec"; `List [`List [`Atom v; exp]]; body] ->
      Letrec (v, aux exp, aux body)
    | `List [`Atom "if"; cond; cons; alt] ->
      If (aux cond, aux cons, aux alt)
    | `List (f :: args) ->
      App (aux f, List.map aux args)
    | e -> failwith ("Cannot parse " ^ (CCSexp.to_string e))
  in match CCSexp.ParseGen.to_list (CCSexp.parse_string s) with
  | `Error err -> failwith err
  | `Ok [] -> failwith "empty source"
  | `Ok (l :: _) -> aux (l : CCSexp.t)

(** Addresses *)
module type AddressSignature = sig
  type t
  val compare : t -> t -> int
  val create : int -> string -> t
  val to_string : t -> string
end

module Address : AddressSignature = struct
  type t = int * string
  let compare = Pervasives.compare
  let create a x = (a, x)
  let to_string (n, x) = x ^ "@" ^ (string_of_int n)
end

(** Environment that map variables to addresses *)
module MakeEnv : functor (A : AddressSignature) ->
sig
  type t
  val empty : t
  val extend : t -> string -> A.t -> t
  val lookup : t -> string -> A.t
  val contains : t -> string -> bool
  val compare : t -> t -> int
end = functor (A : AddressSignature) ->
struct
  type t = A.t StringMap.t
  let empty = StringMap.empty
  let extend env v a = StringMap.add v a env
  let lookup env x = try StringMap.find x env with
    | Not_found -> failwith ("Variable not found: " ^ x)
  let contains env x = StringMap.mem x env
  let compare = StringMap.compare A.compare
end

module Env = MakeEnv(Address)

(** Values *)
module AbstractValue = struct
  type t = [
    | `Closure of lam * Env.t
    | `Primitive of string
    | `Num
    | `Bool
  ]

  let is_true = function
    | _ -> true
  let is_false = function
    | `Bool -> true
    | _ -> false

  let bool _ = `Bool
  let num _ = `Num

  let compare x y = match x, y with
    | `Closure (lam, env), `Closure (lam', env') ->
      order_concat [lazy (Pervasives.compare lam lam');
                    lazy (Env.compare env env')]
    | `Closure _, _ -> 1 | _, `Closure _ -> -1
    | `Primitive f, `Primitive f' -> Pervasives.compare f f'
    | `Primitive _, _ -> 1 | _, `Primitive _ -> -1
    | `Num, `Num -> 0
    | `Num, _ -> 1 | _, `Num -> -1
    | `Bool, `Bool -> 0

  let to_string = function
    | `Closure ((x, e), _) ->
      Printf.sprintf "#<clos %s>" (string_of_exp (Abs (x, e)))
    | `Num -> "Num"
    | `Bool -> "Bool"
    | `Primitive x ->
      Printf.sprintf "#<prim %s>" x

  let op = function
    | "*" | "/" | "+" | "-" -> fun _ -> `Num
    | "=" | "<=" | ">=" | "<" | ">" -> fun _ -> `Bool
    | f -> failwith ("Unknown primitive: " ^ f)

  let max_addr = 0
end

module ConcreteValue = struct
  type t = [
    | `Closure of lam * Env.t
    | `Primitive of string
    | `Int of int
    | `Bool of bool
  ]

  let is_true = function
    | `Bool false -> false
    | _ -> true
  let is_false = function
    | `Bool b -> not b
    | _ -> false

  let bool b = `Bool b
  let num n = `Int n

  let compare x y = match x, y with
    | `Closure (lam, env), `Closure (lam', env') ->
      order_concat [lazy (Pervasives.compare lam lam');
                    lazy (Env.compare env env')]
    | `Closure _, _ -> 1 | _, `Closure _ -> -1
    | `Primitive f, `Primitive f' -> Pervasives.compare f f'
    | `Primitive _, _ -> 1 | _, `Primitive _ -> -1
    | `Int n, `Int n' -> Pervasives.compare n n'
    | `Int _, _ -> 1 | _, `Int _ -> -1
    | `Bool b, `Bool b' -> Pervasives.compare b b'

  let to_string = function
    | `Closure ((x, e), _) ->
      Printf.sprintf "#<clos %s>" (string_of_exp (Abs (x, e)))
    | `Int n -> string_of_int n
    | `Bool b -> string_of_bool b
    | `Primitive x ->
      Printf.sprintf "#<prim %s>" x

  let arith name f x y = match x, y with
    | `Int n, `Int n' ->
      `Int (f n n')
    | _, _ -> failwith (Printf.sprintf "Invalid arithmetic arguments to %s: %s, %s: "
                          name (to_string x) (to_string y))

  let cmp name f = function
    | [`Int n; `Int n'] -> `Bool (f n n')
    | [x; y] -> failwith (Printf.sprintf "Invalid argument types for %s: %s, %s"
                            name (to_string x) (to_string y))
    | n -> failwith (Printf.sprintf "Invalid number of arguments for a comparison operator (expected 2, got %d)"
                       (List.length n))

  let op name =
    match name with
    | "*" -> fun args -> List.fold_left (arith "*" ( * )) (`Int 1) args
    | "+" -> fun args -> List.fold_left (arith "+" (+)) (`Int 0) args
    | "-" -> begin function
        | [] -> failwith "Invalid number of arguments for -"
        | [arg] -> arith "-" (-) (`Int 0) arg
        | arg :: args -> List.fold_left (arith "-" (-)) arg args
      end
    | "/" -> begin function
        | [] -> failwith "Invalid number of arguments for /"
        | [arg] -> arith "/" (/) (`Int 1) arg
        | arg :: args -> List.fold_left (arith "/" (/)) arg args
      end
    | ">" -> cmp ">" (>)
    | ">=" -> cmp ">=" (>=)
    | "<" -> cmp "<" (<)
    | "<=" -> cmp "<=" (<=)
    | "=" -> cmp "=" (=)
    | f -> failwith ("Unknown primitive: " ^ f)

  let max_addr = -1
end

module Value = AbstractValue

(** Lattice *)
module Lattice : sig
  type t
  val join : t -> t -> t
  val compare : t -> t -> int
  val abst : Value.t -> t
  val conc : t -> Value.t list
  val bot : t
  val to_string : t -> string
end = struct
  module VSet = Set.Make(Value)
  type t = VSet.t
  let join v v' = VSet.union v v'
  let compare = VSet.compare
  let abst = VSet.singleton
  let conc v = VSet.elements v
  let bot = VSet.empty
  let to_string v = String.concat "|" (List.map Value.to_string (conc v))
end

(** Store that maps addresses to lattice values *)
module MakeStore : functor (A : AddressSignature) ->
sig
  type t
  val empty : t
  val contains : t -> A.t -> bool
  val lookup : t -> A.t -> Lattice.t
  val join : t -> A.t -> Lattice.t -> t
  val compare : t -> t -> int
end = functor (A : AddressSignature) ->
struct
  module M = Map.Make(A)
  type t = Lattice.t M.t
  let empty = M.empty
  let contains store a = M.mem a store
  let lookup store a = try M.find a store with
    | Not_found -> failwith ("Value not found at address " ^ (A.to_string a))
  let join store a v =
    if contains store a then
      M.add a (Lattice.join v (M.find a store)) store
    else
      M.add a v store
  let compare = M.compare Lattice.compare
end

module Store = MakeStore(Address)

(** Contexts *)
module Context = struct
  type t = {
    lam : lam;
    env : Env.t;
    vals : Lattice.t list;
    store_ts : int;
  }
  let compare ctx ctx' =
    order_concat [lazy (Pervasives.compare ctx.lam ctx'.lam);
                  lazy (Env.compare ctx.env ctx'.env);
                  lazy (compare_list Lattice.compare ctx.vals ctx'.vals);
                  lazy (Pervasives.compare ctx.store_ts ctx'.store_ts)]
  let hash = Hashtbl.hash
  let create lam env vals store_ts = {lam; env; vals; store_ts}
  let to_string ctx =
    Printf.sprintf "ctx(%s, %s)" (Value.to_string (`Closure (ctx.lam, ctx.env)))
      (string_of_list Lattice.to_string ctx.vals)
end

(** Frames *)
module Frame = struct
  type t =
    | AppL of exp list * Env.t
    | AppR of exp list * Lattice.t * Lattice.t list * Env.t
    | Letrec of string * Address.t * exp * Env.t
    | If of exp * exp * Env.t
  let compare x y = match x, y with
    | AppL (exps, env), AppL (exps', env') ->
      order_concat [lazy (Pervasives.compare exps exps');
                    lazy (Env.compare env env')]
    | AppL _, _ -> 1 | _, AppL _ -> -1
    | AppR (exps, f, vs, env), AppR (exps', f', vs', env') ->
      order_concat [lazy (Pervasives.compare exps exps');
                    lazy (Lattice.compare f f');
                    lazy (compare_list Lattice.compare vs vs');
                    lazy (Env.compare env env')]
    | AppR _, _ -> 1 | _, AppR _ -> -1
    | Letrec (x, a, exp, body), Letrec (x', a', exp', body') ->
      order_concat [lazy (Pervasives.compare x x');
                    lazy (Address.compare a a');
                    lazy (Pervasives.compare exp exp');
                    lazy (Pervasives.compare body body')]
    | Letrec _, _ -> 1 | _, Letrec _ -> -1
    | If (cons, alt, env), If (cons', alt', env') ->
      order_concat [lazy (Pervasives.compare cons cons');
                    lazy (Pervasives.compare alt alt');
                    lazy (Env.compare env env')]
  let to_string = function
    | AppL (exps, _) -> Printf.sprintf "AppL(%s)" (string_of_list string_of_exp exps)
    | AppR (exps, _, _, _) -> Printf.sprintf "AppR(%s)" (string_of_list string_of_exp exps)
    | Letrec (name, _, _, _) -> Printf.sprintf "Letrec(%s)" name
    | If (_, _, _) -> Printf.sprintf "If"
end

(** Continuations *)
module Kont = struct
  type t =
    | Empty
    | Ctx of Context.t
  let compare x y = match x, y with
    | Empty, Empty -> 0
    | Empty, _ -> 1 | _, Empty -> -1
    | Ctx ctx, Ctx ctx' ->
      Context.compare ctx ctx'
end

(** Local continuations *)
module LKont = struct
  type t = Frame.t list
  let empty = []
  let is_empty = function
    | [] -> true
    | _ -> false
  let push f lk = f :: lk
  let compare = compare_list Frame.compare
end

(** Continuation store that maps contexts to a pair of
    local continuation and and (normal) continuation *)
module KStore : sig
  type t
  val empty : t
  val lookup : t -> Context.t -> (LKont.t * Kont.t) list
  val join : t -> Context.t -> (LKont.t * Kont.t) -> t
  val compare : t -> t -> int
end = struct
  module M = Map.Make(Context)
  module Pair = struct
    type t = LKont.t * Kont.t
    let compare (lk, k) (lk', k') =
      order_concat [lazy (LKont.compare lk lk');
                    lazy (Kont.compare k k')]
  end
  module S = Set.Make(Pair)
  type t = S.t M.t
  let empty = M.empty
  let lookup kstore ctx = try S.elements (M.find ctx kstore) with
    | Not_found -> failwith "Continuation not found"
  let join kstore ctx k =
    if M.mem ctx kstore then
      M.add ctx (S.add k (M.find ctx kstore)) kstore
    else
      M.add ctx (S.singleton k) kstore
  let compare = M.compare S.compare
end

(** Control part of the CESK state *)
module Control = struct
  type t =
    | Exp of exp
    | Val of Lattice.t
  let compare x y = match x, y with
    | Exp exp, Exp exp' -> Pervasives.compare exp exp'
    | Exp _, _ -> 1 | _, Exp _ -> -1
    | Val v, Val v' -> Lattice.compare v v'
end

(** State of CESK with continuation store.
    We keep the environment component even in value states to simplify the
    implementation, even though it's not necessary *)
module State = struct
  type t = {
    control : Control.t;
    env : Env.t;
    store_ts : int;
    lkont : LKont.t;
    kont : Kont.t;
    time : int;
    kstore_ts : int;
  }

  let compare state state' =
    order_concat [lazy (Control.compare state.control state'.control);
                  lazy (Env.compare state.env state'.env);
                  lazy (Pervasives.compare state.store_ts state'.store_ts);
                  lazy (LKont.compare state.lkont state'.lkont);
                  lazy (Kont.compare state.kont state'.kont);
                  lazy (Pervasives.compare state.time state'.time); (* TODO *)
                  lazy (Pervasives.compare state.kstore_ts state'.kstore_ts)]

  let to_string state = match state.control with
    | Control.Val v -> Lattice.to_string v
    | Control.Exp e -> string_of_exp e
end

module StateSet = Set.Make(State)

(** Graph-generation *)
module Graph = struct
  module G = Graph.Persistent.Digraph.ConcreteBidirectional(struct
      include State
      let hash = Hashtbl.hash
      let equal x y = compare x y == 0
    end)

  module DotArg = struct
    include G
    (* Hack to avoid merging similar states, due to an ocamlgraph bug *)
    module StateMap = Map.Make(State)
    let id = ref 0
    let new_id () =
      id := !id + 1;
      !id
    let nodes = ref StateMap.empty
    let node_id node =
      if StateMap.mem node !nodes then
        StateMap.find node !nodes
      else
        let id = new_id () in
        nodes := StateMap.add node id !nodes;
        id

    let edge_attributes (_ : G.E.t) = []
    let default_edge_attributes _ = []
    let get_subgraph _ = None
    let vertex_name (state : G.V.t) =
      (string_of_int (node_id state))
    let vertex_attributes (state : G.V.t) =
      [`Label (BatString.slice ~last:20 (State.to_string state));
       `Style `Filled]
    let default_vertex_attributes _ = []
    let graph_attributes _ = []
  end

  module Dot = Graph.Graphviz.Dot(DotArg)

  type t = G.t
  let empty = G.empty
  let add_transitions g state successors =
    List.fold_left (fun acc state' -> G.add_edge acc state state') g successors
  let output g file =
    let out = open_out_bin file in
    Dot.output_graph out g;
    close_out out
  let output_stats g =
    Printf.printf "%d/%d\n%!" (G.nb_vertex g) (G.nb_edges g)
end

(** The CESK machine itself *)
module CESK = struct
  open State
  open Control

  (** Tick and alloc implementations *)
  let tick state =
    if Value.max_addr = -1 then
      state.time + 1
    else
      (state.time + 1) mod (Value.max_addr + 1)
  let alloc state x = Address.create state.time x

  (** Injection *)
  let inject exp =
    let primitives = ["*"; "/"; "+"; "-"; "="; "<="; ">="; "<"; ">"] in
    let env, store = List.fold_left (fun (env, store) name ->
        let a = Address.create 0 name in
        (Env.extend env name a, Store.join store a (Lattice.abst (`Primitive name))))
        (Env.empty, Store.empty) primitives in
    { control = Control.Exp exp;
      env = env;
      store_ts = 0;
      lkont = LKont.empty;
      kont = Kont.Empty;
      time = 0;
      kstore_ts = 0; }, store, KStore.empty

  (** Call a primitive with every possible argument value (of module Value) from
      the information given by the lattice *)
  let call_prim f args =
    let rec build_args cur = function
      | [] -> cur
      | hd :: tl ->
        build_args (List.flatten ((List.map (fun l ->
            List.map (fun v -> v :: l) (Lattice.conc hd))
            cur)))
          tl in
    let args' = build_args [[]] args in
    List.map (fun revargs -> Value.op f (List.rev revargs)) args'

  (** Implementation of pop as defined in the paper *)
  module ContextSet = Set.Make(Context)
  module Triple = struct
    type t = Frame.t * LKont.t * Kont.t
    let compare (f, lk, k) (f', lk', k') =
      order_concat [lazy (Frame.compare f f');
                    lazy (LKont.compare lk lk');
                    lazy (Kont.compare k k')]
  end
  module TripleSet = Set.Make(Triple)
  let pop lkont kont kstore =
    let rec pop' lkont kont g = match lkont, kont with
      | [], Kont.Empty -> TripleSet.empty
      | f :: lkont', k -> TripleSet.singleton (f, lkont', k)
      | [], Kont.Ctx ctx ->
        let (part1, g') = List.fold_left (fun (s, g') -> function
            | [], Kont.Ctx ctx when not (ContextSet.mem ctx g) ->
              (s, ContextSet.add ctx g')
            | [], Kont.Ctx _ | [], Kont.Empty -> (s, g')
            | f :: lk, k -> (TripleSet.add (f, lk, k) s, g'))
            (TripleSet.empty, ContextSet.empty) (KStore.lookup kstore ctx) in
        let gug' = ContextSet.union g g' in
        let part2 = ContextSet.fold (fun ctx' acc ->
            TripleSet.union acc (pop' [] (Kont.Ctx ctx') gug'))
            g' TripleSet.empty in
        TripleSet.union part1 part2 in
    pop' lkont kont ContextSet.empty

  (** Step a continuation state *)
  let step_kont state store kstore v frame lkont kont =
    match frame with
    | Frame.AppL (arg :: args, env) ->
      let lkont = LKont.push (Frame.AppR (args, v, [], state.env)) lkont in
      [{state with control = Exp arg; env; lkont; kont}], store, kstore
    | Frame.AppL ([], env) ->
      failwith "TODO: functions with 0 arguments not yet implemented"
    | Frame.AppR (arg :: args, clo, argsv, env) ->
      let lkont = LKont.push (Frame.AppR (args, clo, v :: argsv, env)) lkont in
      [{state with control = Exp arg; env; lkont; kont}], store, kstore
    | Frame.AppR ([], clo, args', env) ->
      let args = List.rev (v :: args') in
      let store = ref store in
      let kstore = ref kstore in
      let res = List.flatten (List.map (function
          | `Closure ((xs, body), env') ->
            (* the only tricky case: we need to push the local continuation in
               the continuation store, and then replace the local cont by an
               empty one *)
            if List.length xs != List.length args then
              failwith (Printf.sprintf
                          "Arity mismatch: expected %d argument, got %d"
                          (List.length xs) (List.length args))
            else
              let env'' = List.fold_left2 (fun env x v ->
                  let a = alloc state x in
                  store := Store.join !store a v;
                  Env.extend env x a)
                  env' xs args in
              let ctx = Context.create (xs, body) env' args state.store_ts in
              (* Error in the paper: they extend the stack store with
                 (state.lkont, state.kont), therefore forgetting to remove the
                 AppR that is on top of the stack *)
              kstore := KStore.join !kstore ctx (lkont, state.kont);
              [{control = Exp body; env = env''; store_ts = state.store_ts + 1;
                kstore_ts = state.kstore_ts + 1 ;
                lkont = LKont.empty; kont = Kont.Ctx ctx; time = tick state}]
          | `Primitive f ->
            (* in the case of a primitive call, we don't need to step into a
               function's body and can therefore leave the stack unchanged
               (except for the pop) *)
            let results = call_prim f args in
            List.map (fun res ->
                {state with control = Val (Lattice.abst res); lkont; kont;
                            time = tick state})
              results
          | _ -> [])
          (Lattice.conc clo)) in
       res, !store, !kstore
    | Frame.Letrec (x, a, body, env) ->
      let store' = Store.join store a v in
      [{state with control = Exp body; store_ts = state.store_ts + 1;
                   env; lkont; kont; time = tick state}], store', kstore
    | Frame.If (cons, alt, env) ->
      let t = {state with control = Exp cons; env; lkont; kont; time = tick state}
      and f = {state with control = Exp alt;  env; lkont; kont; time = tick state} in
      List.flatten (List.map (fun v ->
          if Value.is_true v && Value.is_false v then
            [t; f]
          else if Value.is_true v then
            [t]
          else if Value.is_false v then
            [f]
          else
            []) (Lattice.conc v)), store, kstore

  (** Step an evaluation state *)
  let step_eval state store kstore = function
    | Var x ->
      let v = Store.lookup store (Env.lookup state.env x) in
      [{state with control = Val v; time = tick state}], store, kstore
    | Int n ->
      [{state with control = Val (Lattice.abst (Value.num n)); time = tick state}], store, kstore
    | Bool b ->
      [{state with control = Val (Lattice.abst (Value.bool b)); time = tick state}], store, kstore
    | Abs lam ->
      [{state with control = Val (Lattice.abst (`Closure (lam, state.env)));
                   time = tick state}], store, kstore
    | App (f, args) ->
      let lkont = LKont.push (Frame.AppL (args, state.env)) state.lkont in
      [{state with control = Exp f; lkont; time = tick state}], store, kstore
    | Letrec (x, exp, body) ->
      let a = alloc state x in
      let env = Env.extend state.env x a in
      let store' = Store.join store a Lattice.bot in
      let lkont = LKont.push (Frame.Letrec (x, a, body, env)) state.lkont in
      [{state with control = Exp exp; env; store_ts = state.store_ts + 1;
                   lkont; time = tick state}], store', kstore
    | If (cond, cons, alt) ->
      let lkont = LKont.push (Frame.If (cons, alt, state.env)) state.lkont in
      [{state with control = Exp cond; lkont; time = tick state}], store, kstore

  (** Main step function *)
  let step state store kstore = match state.control with
    | Exp exp -> step_eval state store kstore exp
    | Val v ->
      let popped = pop state.lkont state.kont kstore in
      let store = ref store in
      let kstore = ref kstore in
      let stepped = List.flatten (List.map (fun (frame, lkont, kont) ->
          let res, store', kstore' = step_kont state !store !kstore v frame lkont kont in
          store := store';
          kstore := kstore';
          res)
          (TripleSet.elements popped)) in
      (* OCaml evaluates tuples right-to-left! *)
      stepped, !store, !kstore

  (** Simple work-list state space exploration *)
  let run exp =
    let rec loop visited todo store kstore graph finals =
      if StateSet.is_empty todo then
        (graph, finals)
      else
        let state = StateSet.choose todo in
        let rest = StateSet.remove state todo in
        if StateSet.mem state visited then
          loop visited rest store kstore graph finals
        else begin
          (* Printf.printf "Stepping %s" (State.to_string state); *)
          begin match step state store kstore with
            | [], store, kstore ->
              (* Printf.printf "final state\n%!";*)
              loop (StateSet.add state visited) rest store kstore graph (state :: finals)
            | stepped, store, kstore ->
              (* Printf.printf "%s\n%!"
                (String.concat ", " (List.map State.to_string stepped)); *)
              loop (StateSet.add state visited)
                (StateSet.union (StateSet.of_list stepped) rest)
                store kstore
                (Graph.add_transitions graph state stepped)
                finals
          end
        end in
    let initial, store, kstore = inject exp in
    loop StateSet.empty (StateSet.singleton initial) store kstore Graph.empty []
end

let run name source =
  let (graph, finals) = CESK.run (parse source) in
  Printf.printf "%s: %s " name (String.concat "|"
                                     (List.map State.to_string finals));
  Graph.output graph (name ^ ".dot");
  Graph.output_stats graph

let () =
  run "add" "(+ 1 2)";
  run "letrec" "(letrec ((x 1)) x)";
  run "letrec" "(letrec ((x 1)) (letrec ((y 2)) (+ x y)))";
  run "if" "(if #t 1 2)";
  run "fun" "((lambda (x) #t) 1)";
  run "simple" "(letrec ((f (lambda (x y) (if x x y)))) (f #t 3))";
  run "sq" "((lambda (x) (* x x)) 8)";
(*  run "loopy1" "(letrec ((f (lambda (x) (f x)))) (f 1))"; *)
(*  run "loopy2" "((lambda (x) (x x)) (lambda (y) (y y)))"; *)
  run "fac" "(letrec ((fac (lambda (n) (if (= n 0) 1 (* n (fac (- n 1))))))) (fac 8))";
  run "fib" "(letrec ((fib (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))) (fib 8))";
  run "safeloopy1" "(letrec ((count (lambda (n) (letrec ((t (= n 0))) (if t 123 (letrec ((u (- n 1))) (letrec ((v (count u))) v))))))) (count 8))";
  ()
