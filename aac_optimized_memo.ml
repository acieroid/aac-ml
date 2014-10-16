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
  val ts : t -> int
end = functor (A : AddressSignature) ->
struct
  module M = Map.Make(A)
  type t = {
    store : Lattice.t M.t;
    ts : int;
  }
  let empty = {store = M.empty; ts = 0}
  let contains store a = M.mem a store.store
  let lookup store a = try M.find a store.store with
    | Not_found -> failwith ("Value not found at address " ^ (A.to_string a))
  let join store a v =
    if contains store a then
      let oldval = M.find a store.store in
      let newval = Lattice.join v oldval in
      {store = M.add a newval store.store;
       ts = if Lattice.compare oldval newval == 0 then store.ts else store.ts + 1}
    else
      {store = M.add a v store.store; ts = store.ts + 1}
  let compare store store' =
    order_concat [lazy (Pervasives.compare store.ts store'.ts);
                  lazy (M.compare Lattice.compare store.store store'.store)]
  let ts store = store.ts
end

module Store = MakeStore(Address)

(** Contexts *)
module Context = struct
  type t =
    (** A context created at a call site *)
    | Call of exp * Env.t * Store.t
    (** A context created at an application site *)
    | App of lam * Env.t * Lattice.t list * Store.t
  let compare x y = match x, y with
    | Call (exp, env, store), Call (exp', env', store') ->
      order_concat [lazy (Pervasives.compare exp exp');
                    lazy (Env.compare env env');
                    lazy (Store.compare store store')]
    | Call _, _ -> 1 | _, Call _ -> -1
    | App (lam, env, args, store), App (lam', env', args', store') ->
      order_concat [lazy (Pervasives.compare lam lam');
                    lazy (Env.compare env env');
                    lazy (compare_list Lattice.compare args args');
                    lazy (Store.compare store store')]
  let hash = Hashtbl.hash
  let create_app lam env args store = App (lam, env, args, store)
  let create_call exp env store = Call (exp, env, store)
  let to_string = function
    | App (lam, env, args, store) ->
      Printf.sprintf "ctx_call(%s, %s)" (Value.to_string (`Closure (lam, env)))
        (string_of_list Lattice.to_string args)
    | Call (exp, env, store) ->
      Printf.sprintf "ctx_app(%s)" (string_of_exp exp)
end

(** Memoization results *)
module Relevant = struct
  type t = exp * Env.t * Store.t
  let compare (e, env, store) (e', env', store') =
    order_concat [lazy (Pervasives.compare e e');
                  lazy (Env.compare env env');
                  lazy (Store.compare store store')]
end

(** Memo table *)
module Memo : sig
  type t
  val empty : t
  val ts : t -> int
  val contains : t -> Context.t -> bool
  val lookup : t -> Context.t -> Relevant.t list
  val join : t -> Context.t -> Relevant.t -> t
end = struct
  module M = Map.Make(Context)
  module S = Set.Make(Relevant)
  type t = {
    memo : S.t M.t;
    ts : int;
  }
  let empty = {memo = M.empty; ts = 0}
  let ts memo = memo.ts
  let contains memo ctx = M.mem ctx memo.memo
  let lookup memo ctx = try S.elements (M.find ctx memo.memo) with
  | Not_found -> failwith "Cannot find memoized context"
  let join memo ctx relevant =
    if contains memo ctx then
      let oldval = M.find ctx memo.memo in
      let newval = S.add relevant oldval in
      {memo = M.add ctx newval memo.memo;
       ts = if S.compare newval oldval == 0 then memo.ts else memo.ts + 1}
    else
      {memo = M.add ctx (S.singleton relevant) memo.memo;
       ts = memo.ts + 1}

  let compare memo memo' =
    order_concat [lazy (M.compare S.compare memo.memo memo'.memo);
                  lazy (Pervasives.compare memo.ts memo'.ts)]
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
  val ts : t -> int
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
  type t = {
    kstore : S.t M.t;
    ts : int;
  }
  let empty = {kstore = M.empty; ts = 0}
  let lookup kstore ctx = try S.elements (M.find ctx kstore.kstore) with
    | Not_found -> failwith "Continuation not found"
  let join kstore ctx k =
    if M.mem ctx kstore.kstore then
      let oldval = M.find ctx kstore.kstore in
      let newval = S.add k oldval in
      {kstore = M.add ctx newval kstore.kstore;
       ts = if S.compare oldval newval == 0 then kstore.ts else kstore.ts + 1}
    else
      {kstore = M.add ctx (S.singleton k) kstore.kstore;
       ts = kstore.ts + 1}
  let ts kstore = kstore.ts
  let compare kstore kstore' =
    order_concat [lazy (Pervasives.compare kstore.ts kstore'.ts);
                  lazy (M.compare S.compare kstore.kstore kstore'.kstore)]
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
    store : Store.t;
    lkont : LKont.t;
    kont : Kont.t;
    time : int;
    kstore_ts : int;
    memo_ts : int;
  }

  let compare state state' =
    order_concat [lazy (Control.compare state.control state'.control);
                  lazy (Env.compare state.env state'.env);
                  lazy (Store.compare state.store state'.store);
                  lazy (LKont.compare state.lkont state'.lkont);
                  lazy (Kont.compare state.kont state'.kont);
                  lazy (Pervasives.compare state.time state'.time); (* TODO *)
                  lazy (Pervasives.compare state.kstore_ts state'.kstore_ts);
                  lazy (Pervasives.compare state.memo_ts state'.memo_ts)]

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
    let kstore = KStore.empty in
    let memo = Memo.empty in
    { control = Control.Exp exp;
      env = env;
      store = store;
      lkont = LKont.empty;
      kont = Kont.Empty;
      time = 0;
      kstore_ts = KStore.ts kstore;
      memo_ts = Memo.ts memo}, kstore, memo

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
    TODO
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
  let step_kont state kstore memo v frame lkont kont =
    match frame with
    | Frame.AppL (arg :: args, env) ->
      let lkont = LKont.push (Frame.AppR (args, v, [], state.env)) lkont in
      [{state with control = Exp arg; env; lkont; kont}], kstore, memo
    | Frame.AppL ([], env) ->
      failwith "TODO: functions with 0 arguments not yet implemented"
    | Frame.AppR (arg :: args, clo, argsv, env) ->
      let lkont = LKont.push (Frame.AppR (args, clo, v :: argsv, env)) lkont in
      [{state with control = Exp arg; env; lkont; kont}], kstore, memo
    | Frame.AppR ([], clo, args', env) ->
      let args = List.rev (v :: args') in
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
              let (env'', store') = List.fold_left2 (fun (env, store) x v ->
                  let a = alloc state x in
                  (Env.extend env x a,
                   Store.join store a v))
                  (env', state.store) xs args in
              let ctx = Context.create_app (xs, body) env' args state.store in
              (* Error in the paper: they extend the stack store with
                 (state.lkont, state.kont), therefore forgetting to remove the
                 AppR that is on top of the stack *)
              kstore := KStore.join !kstore ctx (lkont, state.kont);
              [{control = Exp body; env = env''; store = store';
                kstore_ts = KStore.ts !kstore;
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
       res, !kstore, !memo
    | Frame.Letrec (x, a, body, env) ->
      let store = Store.join state.store a v in
      [{state with control = Exp body; store;
                   env; lkont; kont; time = tick state}], kstore, memo
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
            []) (Lattice.conc v)), kstore, memo

  (** Step an evaluation state *)
  let step_eval state kstore memo = function
    | Var x ->
      let v = Store.lookup state.store (Env.lookup state.env x) in
      [{state with control = Val v; time = tick state}], kstore, memo
    | Int n ->
      [{state with control = Val (Lattice.abst (Value.num n)); time = tick state}], kstore, memo
    | Bool b ->
      [{state with control = Val (Lattice.abst (Value.bool b)); time = tick state}], kstore, memo
    | Abs lam ->
      [{state with control = Val (Lattice.abst (`Closure (lam, state.env)));
                   time = tick state}], kstore, memo
    | App (f, args) ->
      (* Lookup in the memo table to see if we can shortcut this execution *)
      (* TODO: the paper says "at memo-use time, still extend Ξ so later memo
        table extensions will flow to previous memo table uses". However, with
        the CESIK*Ξ machine, Ξ is not extended during function application. *)
      let ctx = Context.create_call (App (f, args)) state.env state.store in
      if Memo.contains memo ctx then
        let relevants = Memo.lookup memo ctx in
        List.map (fun (e', env', store') ->
            {state with control = Exp e'; env = env'; store = store'})
          relevants, kstore, memo
      else
        let lkont = LKont.push (Frame.AppL (args, state.env)) state.lkont in
        [{state with control = Exp f; lkont; time = tick state}], kstore, memo
    | Letrec (x, exp, body) ->
      let a = alloc state x in
      let env = Env.extend state.env x a in
      let store' = Store.join state.store a Lattice.bot in
      let lkont = LKont.push (Frame.Letrec (x, a, body, env)) state.lkont in
      [{state with control = Exp exp; env; store = store';
                   lkont; time = tick state}], kstore, memo
    | If (cond, cons, alt) ->
      let lkont = LKont.push (Frame.If (cons, alt, state.env)) state.lkont in
      [{state with control = Exp cond; lkont; time = tick state}], kstore, memo

  (** Main step function *)
  let step state kstore memo = match state.control with
    | Exp exp -> step_eval state kstore memo exp
    | Val v ->
      let popped = pop state.lkont state.kont kstore in
      let kstore = ref kstore in
      let memo = ref memo in
      let stepped = List.flatten (List.map (fun (frame, lkont, kont) ->
          let res, kstore', memo' = step_kont state !kstore !memo v frame lkont kont in
          kstore := kstore';
          memo := memo';
          res)
          (TripleSet.elements popped)) in
      (* OCaml evaluates tuples right-to-left! *)
      stepped, !kstore, !memo

  (** Simple work-list state space exploration *)
  let run exp =
    let rec loop visited todo kstore memo graph finals =
      if StateSet.is_empty todo then
        (graph, finals)
      else
        let state = StateSet.choose todo in
        let rest = StateSet.remove state todo in
        if StateSet.mem state visited then
          loop visited rest kstore memo graph finals
        else begin
          (* Printf.printf "Stepping %s" (State.to_string state); *)
          begin match step state kstore memo with
            | [], kstore, memo ->
              (* Printf.printf "final state\n%!";*)
              loop (StateSet.add state visited) rest kstore memo graph (state :: finals)
            | stepped, kstore, memo ->
              (* Printf.printf "%s\n%!"
                (String.concat ", " (List.map State.to_string stepped)); *)
              loop (StateSet.add state visited)
                (StateSet.union (StateSet.of_list stepped) rest)
                kstore memo
                (Graph.add_transitions graph state stepped)
                finals
          end
        end in
    let initial, kstore, memo = inject exp in
    loop StateSet.empty (StateSet.singleton initial) kstore memo Graph.empty []
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
  run "loopy1" "(letrec ((f (lambda (x) (f x)))) (f 1))";
  run "loopy2" "((lambda (x) (x x)) (lambda (y) (y y)))";
  run "fac" "(letrec ((fac (lambda (n) (if (= n 0) 1 (* n (fac (- n 1))))))) (fac 8))";
  run "fib" "(letrec ((fib (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))) (fib 8))";
  run "safeloopy1" "(letrec ((count (lambda (n) (letrec ((t (= n 0))) (if t 123 (letrec ((u (- n 1))) (letrec ((v (count u))) v))))))) (count 8))";
  ()