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
    | `List [`Atom "let"; `List [`List [`Atom v; exp]]; body]
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
    | "*" | "/" | "+" | "-" | "log" | "modulo" | "ceiling" | "random" -> fun _ -> `Num
    | "=" | "<=" | ">=" | "<" | ">" | "not" | "even?" | "odd?" -> fun _ -> `Bool
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
  type t = {
    exp : exp;
    env : Env.t;
    store : Store.t;
    time : int; (* TODO *)
  }
  let compare ctx ctx' =
    order_concat [lazy (Pervasives.compare ctx.exp ctx'.exp);
                  lazy (Env.compare ctx.env ctx'.env);
                  lazy (Store.compare ctx.store ctx'.store)]
  let hash = Hashtbl.hash
  let create exp env store time = {exp; env; store; time}
  let to_string ctx =
    Printf.sprintf "ctx(%s, %s, %d, %d)" (string_of_exp ctx.exp) (string_of_int ctx.time) (Store.ts ctx.store) ctx.time
end

module ContextSet = Set.Make(Context)

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
end

(** Continuations *)
module Kont = struct
  type t =
    | Empty
    | Cons of Frame.t * Context.t
  let compare x y = match x, y with
    | Empty, Empty -> 0
    | Empty, _ -> 1 | _, Empty -> -1
    | Cons (f, ctx), Cons (f', ctx') ->
      order_concat [lazy (Frame.compare f f');
                    lazy (Context.compare ctx ctx')]
end

(** Continuation store *)
module KStore : sig
  type t
  val empty : t
  val lookup : t -> Context.t -> Kont.t list
  val join : t -> Context.t -> Kont.t -> t
  val domain : t -> ContextSet.t
  val compare : t -> t -> int
  val ts : t -> int
  (* Return a delta kstore, containing what has been added between the first and
     second argument *)
  val delta : t -> t -> t
end = struct
  module M = Map.Make(Context)
  module S = Set.Make(Kont)
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
  let domain kstore =
    M.fold (fun ctx _ acc -> ContextSet.add ctx acc) kstore.kstore ContextSet.empty
  let compare kstore kstore' =
    order_concat [lazy (Pervasives.compare kstore.ts kstore'.ts);
                  lazy (M.compare S.compare kstore.kstore kstore'.kstore)]
  let ts kstore = kstore.ts
  let delta kstore kstore' =
    {kstore =
       if kstore.ts == kstore'.ts then
         M.empty
       else
         M.merge (fun ctx ks ks' -> match ks, ks' with
             (* Those case shouldn't happen (the store only grows) *)
             | None, None | Some _, None -> None
             | None, Some x -> Some x
             | Some x, Some y when S.equal x y -> None
             | Some x, Some y -> Some (S.diff y x))
           kstore.kstore kstore'.kstore;
     ts = 0}
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
  val domain : t -> ContextSet.t
  val join : t -> Context.t -> Relevant.t -> t
  val delta : t -> t -> t
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
  let domain memo =
    M.fold (fun ctx _ acc -> ContextSet.add ctx acc) memo.memo ContextSet.empty

  let compare memo memo' =
    order_concat [lazy (M.compare S.compare memo.memo memo'.memo);
                  lazy (Pervasives.compare memo.ts memo'.ts)]

  let delta memo memo' =
    {memo = M.merge (fun ctx ks ks' -> match ks, ks' with
         (* Those case shouldn't happen (the store only grows) *)
         | None, None | Some _, None -> None
         | None, Some x -> Some x
         | Some x, Some y when S.equal x y -> None
         | Some x, Some y -> Some (S.diff y x))
         memo.memo memo'.memo;
     ts = 0}
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
    kont : Kont.t;
    time : int;
    kstore_ts : int;
    memo_ts : int;
  }

  let compare state state' =
    order_concat [lazy (Pervasives.compare state.time state'.time); (* TODO *)
                  lazy (Pervasives.compare state.kstore_ts state'.kstore_ts);
                  lazy (Pervasives.compare state.memo_ts state'.memo_ts);
                  lazy (Control.compare state.control state'.control);
                  lazy (Env.compare state.env state'.env);
                  lazy (Store.compare state.store state'.store);
                  lazy (Kont.compare state.kont state'.kont)]

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
    let primitives = ["*"; "/"; "+"; "-"; "="; "<="; ">="; "<"; ">"; "not"; "random"; "modulo"; "ceiling"; "even?"; "odd?"; "log"] in
    let env, store = List.fold_left (fun (env, store) name ->
        let a = Address.create 0 name in
        (Env.extend env name a, Store.join store a (Lattice.abst (`Primitive name))))
        (Env.empty, Store.empty) primitives in
    let kstore = KStore.empty in
    let memo = Memo.empty in
    { control = Control.Exp exp;
      env = env;
      store = store;
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

  (** Step function *)
  let step state kstore memo = match state.control with
    | Exp (Var x) ->
      let v = Store.lookup state.store (Env.lookup state.env x) in
      [{state with control = Val v; time = tick state}], kstore, memo
    | Exp (Int n) ->
      [{state with control = Val (Lattice.abst (Value.num n));
                   time = tick state}], kstore, memo
    | Exp (Bool b) ->
      [{state with control = Val (Lattice.abst (Value.bool b));
                   time = tick state}], kstore, memo
    | Exp (Abs lam) ->
      [{state with control = Val (Lattice.abst (`Closure (lam, state.env)));
                   time = tick state}], kstore, memo
    | Exp (App (f, args)) ->
      (* Consult the memo table *)
      let ctx = Context.create (App (f, args)) state.env state.store state.time in
      let kstore' = KStore.join kstore ctx state.kont in
      (* In the paper, the kstore is only updated with a memo hit.
         This is probably a typo, because then the continuations will never be
         pushed in the continuation store if no memo hit happens.
         We therefore also update the kstore when the memo table does not
         contain the context.
         It is even not necessary to update the kstore when the context is
         present in the memo table, because we won't touch the contiunaition
         of the state *)
      if Memo.contains memo ctx then
        (* Memo hit *)
        List.map (fun (e', env', store') ->
            {state with control = Exp e'; env = env'; store = store'; time = tick state})
          (Memo.lookup memo ctx),
        kstore, memo
      else
        let kont = Kont.Cons (Frame.AppL (args, state.env), ctx) in
        [{state with control = Exp f; kont; kstore_ts = KStore.ts kstore';
                     time = tick state}], kstore', memo
    | Exp (Letrec (x, exp, body)) ->
      let ctx = Context.create (Letrec (x, exp, body)) state.env state.store state.time in
      let a = alloc state x in
      let env = Env.extend state.env x a in
      let store = Store.join state.store a Lattice.bot in
      let kont = Kont.Cons (Frame.Letrec (x, a, body, env), ctx) in
      let kstore' = KStore.join kstore ctx state.kont in
      [{state with control = Exp exp; env; store; kont; kstore_ts = KStore.ts kstore';
                   time = tick state}], kstore', memo
    | Exp (If (cond, cons, alt)) ->
      let ctx = Context.create (If (cond, cons, alt)) state.env state.store state.time in
      let kont = Kont.Cons (Frame.If (cons, alt, state.env), ctx) in
      let kstore' = KStore.join kstore ctx state.kont in
      [{state with control = Exp cond; kont; kstore_ts = KStore.ts kstore';
                   time = tick state}], kstore', memo
    | Val v -> begin match state.kont with
        | Kont.Empty -> [], kstore, memo (* Evaluation finished? *)
        | Kont.Cons (Frame.AppL (arg :: args, env), ctx) ->
          let kont = Kont.Cons (Frame.AppR (args, v, [], env), ctx) in
          [{state with control = Exp arg; env; kont}], kstore, memo
        | Kont.Cons (Frame.AppL ([], env), ctx) ->
          failwith "TODO: functions with 0 arguments are NYI"
        | Kont.Cons (Frame.AppR (arg :: args, clo, argsv, env), ctx) ->
          let kont = Kont.Cons (Frame.AppR (args, clo, v :: argsv, env), ctx) in
          [{state with control = Exp arg; env; kont}], kstore, memo
        | Kont.Cons (Frame.AppR ([], clo, args', env), ctx) ->
          let args = List.rev (v :: args') in
          let konts = KStore.lookup kstore ctx in
          let memo = ref memo in
          let res = List.flatten (List.map (fun kont ->
              List.flatten
                (List.map (function
                     | `Closure ((xs, body), env') ->
                       if List.length xs != List.length args then
                         []
                       else
                         let (env'', store) = List.fold_left2 (fun (env, store) x v ->
                             let a = alloc state x in
                             (Env.extend env x a,
                              Store.join store a v))
                             (env', state.store) xs args in
                         (* Update the memo table *)
                         memo := Memo.join !memo ctx (body, env'', store);
                         [{state with control = Exp body; env = env'';
                                      store; kont; time = tick state}]
                     | `Primitive f ->
                       let results = call_prim f args in
                       List.map (fun res ->
                           {state with control = Val (Lattice.abst res); kont;
                                       time = tick state})
                         results
                     | _ -> [])
                    (Lattice.conc clo)))
              konts) in
          res, kstore, !memo
        | Kont.Cons (Frame.Letrec (x, a, body, env), ctx) ->
          let store = Store.join state.store a v in
          let konts = KStore.lookup kstore ctx in
          List.map (fun kont ->
              {state with control = Exp body; store; env; kont;
                          time = tick state})
            konts, kstore, memo
        | Kont.Cons (Frame.If (cons, alt, env), ctx) ->
          let konts = KStore.lookup kstore ctx in
          List.flatten (List.map (fun kont ->
              let t = {state with control = Exp cons; env; kont; time = tick state}
              and f = {state with control = Exp alt;  env; kont; time = tick state} in
              List.flatten (List.map (fun v ->
                  if Value.is_true v && Value.is_false v then
                    [t; f]
                  else if Value.is_true v then
                    [t]
                  else if Value.is_false v then
                    [f]
                  else
                    []) (Lattice.conc v)))
              konts), kstore, memo
      end

  (** Simple work-list state space exploration *)
  (* TODO: This should be adapted to visit states already visited, depending on
     what has been added to the memo table *)
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
          (* Printf.printf "Stepping %s: " (State.to_string state); *)
          begin match step state kstore memo with
            | [], kstore', memo' ->
              (* Printf.printf "final state\n%!"; *)
              let dkstore = KStore.delta kstore kstore' in
              let dmemo = Memo.delta memo memo' in
              let delta = ContextSet.inter (KStore.domain dkstore)
                  (Memo.domain dmemo) in
              let to_add = ContextSet.fold (fun ctx acc ->
                  let relevants = Memo.lookup dmemo ctx in
                  let konts = KStore.lookup dkstore ctx in
                  List.fold_left (fun acc (exp, env, store) ->
                      List.fold_left (fun acc kont ->
                          StateSet.add {control = Exp exp;
                                        env; store; kont;
                                        (* TODO: what should those value be?
                                           Ideally, we should look into the
                                           state graph and extract every state
                                           that matches (exp, env, store, kont).
                                        *)
                                        time = 0;
                                        kstore_ts = KStore.ts kstore';
                                        memo_ts = Memo.ts memo'}
                            acc) acc konts)
                    acc relevants) delta StateSet.empty in
              let to_add = StateSet.empty in
              loop (StateSet.add state visited) (StateSet.union to_add rest)
              kstore' memo' graph (state :: finals)
            | stepped, kstore', memo' ->
              (* Printf.printf "%s\n%!"
                (String.concat ", " (List.map State.to_string stepped)); *)
              loop (StateSet.add state visited)
                (StateSet.union (StateSet.of_list stepped) rest)
                kstore' memo'
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
  run "sq" "((lambda (x) (* x x)) 8)";
  run "loopy1" "(letrec ((f (lambda (x) (f x)))) (f 1))";
  run "loopy2" "((lambda (x) (x x)) (lambda (y) (y y)))";
  run "fac" "(letrec ((fac (lambda (n) (if (= n 0) 1 (* n (fac (- n 1))))))) (fac 8))";
  run "fib" "(letrec ((fib (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))) (fib 8))";
  run "safeloopy1" "(letrec ((count (lambda (n) (letrec ((t (= n 0))) (if t 123 (letrec ((u (- n 1))) (letrec ((v (count u))) v))))))) (count 8))";
  run "eta" "(let ((_do-something0 (lambda (x) 10))) (let ((_id1 (lambda (_y2) (let ((_tmp13 (_do-something0 1))) _y2)))) (let ((_p7 (_id1 (lambda (_a5) _a5)))) (let ((_tmp24 (_p7 #t))) (let ((_p8 (_id1 (lambda (_b6) _b6)))) (_p8 #f))))))";
  run "fac" "(letrec ((fac (lambda (n) (let ((t (= n 0))) (if t 1 (let ((u (- n 1))) (let ((v (fac u))) (* n v)))))))) (fac 10))";
  run "fib" "(letrec ((_fib0 (lambda (_n1) (let ((_p2 (< _n1 2))) (if _p2 _n1 (let ((_p3 (- _n1 1))) (let ((_p4 (_fib0 _p3))) (let ((_p5 (- _n1 2))) (let ((_p6 (_fib0 _p5))) (+ _p4 _p6)))))))))) (_fib0 4))";
  run "gcIpdExample" "(let ((_id0 (lambda (_x1) _x1))) (letrec ((_f2 (lambda (_n3) (let ((_p6 (<= _n3 1))) (if _p6 1 (let ((_p7 (- _n3 1))) (let ((_p8 (_f2 _p7))) (* _n3 _p8)))))))) (letrec ((_g4 (lambda (_n5) (let ((_p9 (<= _n5 1))) (if _p9 1 (let ((_p10 (* _n5 _n5))) (let ((_p11 (- _n5 1))) (let ((_p12 (_g4 _p11))) (+ _p10 _p12))))))))) (let ((_p13 (_id0 _f2))) (let ((_p14 (_p13 3))) (let ((_p15 (_id0 _g4))) (let ((_p16 (_p15 4))) (+ _p14 _p16))))))))";
  run "kcfa2" "(let ((_f10 (lambda (_x12) (let ((_f23 (lambda (_x26) (let ((_z7 (lambda (_y18 _y29) _y18))) (_z7 _x12 _x26))))) (let ((_b4 (_f23 #t))) (let ((_c5 (_f23 #f))) (_f23 #t))))))) (let ((_a1 (_f10 #t))) (_f10 #f)))";
  run "kcfa3" "(let ((_f10 (lambda (_x12) (let ((_f23 (lambda (_x25) (let ((_f36 (lambda (_x38) (let ((_z9 (lambda (_y110 _y211 _y312) _y110))) (_z9 _x12 _x25 _x38))))) (let ((_c7 (_f36 #t))) (_f36 #f)))))) (let ((_b4 (_f23 #t))) (_f23 #f)))))) (let ((_a1 (_f10 #t))) (_f10 #f)))";
  run "loop2" "(letrec ((_lp10 (lambda (_i1 _x2) (let ((_a3 (= 0 _i1))) (if _a3 _x2 (letrec ((_lp24 (lambda (_j5 _f6 _y7) (let ((_b8 (= 0 _j5))) (if _b8 (let ((_p10 (- _i1 1))) (_lp10 _p10 _y7)) (let ((_p11 (- _j5 1))) (let ((_p12 (_f6 _y7))) (_lp24 _p11 _f6 _p12)))))))) (_lp24 10 (lambda (_n9) (+ _n9 _i1)) _x2))))))) (_lp10 10 0))";
  run "mj09" "(let ((_h0 (lambda (_b1) (let ((_g2 (lambda (_z3) _z3))) (let ((_f4 (lambda (_k5) (if _b1 (_k5 1) (_k5 2))))) (let ((_y6 (_f4 (lambda (_x7) _x7)))) (_g2 _y6))))))) (let ((_x8 (_h0 #t))) (let ((_y9 (_h0 #f))) _y9)))";
  run "blur" "(let ((_id0 (lambda (_x1) _x1))) (let ((_blur2 (lambda (_y3) _y3))) (letrec ((_lp4 (lambda (_a5 _n6) (let ((_p9 (<= _n6 1))) (if _p9 (_id0 _a5) (let ((_p10 (_blur2 _id0))) (let ((_r7 (_p10 #t))) (let ((_p11 (_blur2 _id0))) (let ((_s8 (_p11 #f))) (let ((_p12 (_blur2 _lp4))) (let ((_p13 (- _n6 1))) (let ((_p14 (_p12 _s8 _p13))) (not _p14))))))))))))) (_lp4 #f 2))))";
  run "rotate" "(letrec ((_rotate0 (lambda (_n1 _x2 _y3 _z4) (let ((_p5 (= _n1 0))) (if _p5 _x2 (let ((_p6 (- _n1 1))) (_rotate0 _p6 _y3 _z4 _x2))))))) (_rotate0 41 5 #t #f))";
  run "sat" "(let ((_phi5 (lambda (_x16 _x27 _x38 _x49) (let ((__t010 _x16)) (let ((_p23 (if __t010 __t010 (let ((__t111 (not _x27))) (if __t111 __t111 (not _x38)))))) (if _p23 (let ((__t212 (not _x27))) (let ((_p24 (if __t212 __t212 (not _x38)))) (if _p24 (let ((__t313 _x49)) (if __t313 __t313 _x27)) #f))) #f)))))) (let ((_try14 (lambda (_f15) (let ((__t416 (_f15 #t))) (if __t416 __t416 (_f15 #f)))))) (let ((_sat-solve-417 (lambda (_p18) (_try14 (lambda (_n119) (_try14 (lambda (_n220) (_try14 (lambda (_n321) (_try14 (lambda (_n422) (_p18 _n119 _n220 _n321 _n422)))))))))))) (_sat-solve-417 _phi5))))";
  run "primtest" "(let ((_square9 (lambda (_x10) (* _x10 _x10)))) (letrec ((_modulo-power11 (lambda (_base12 _exp13 _n14) (let ((_p37 (= _exp13 0))) (if _p37 1 (let ((_p38 (odd? _exp13))) (if _p38 (let ((_p39 (- _exp13 1))) (let ((_p40 (_modulo-power11 _base12 _p39 _n14))) (let ((_p41 (* _base12 _p40))) (modulo _p41 _n14)))) (let ((_p42 (/ _exp13 2))) (let ((_p43 (_modulo-power11 _base12 _p42 _n14))) (let ((_p44 (_square9 _p43))) (modulo _p44 _n14))))))))))) (let ((_is-trivial-composite?15 (lambda (_n16) (let ((_p45 (modulo _n16 2))) (let ((__t017 (= _p45 0))) (if __t017 __t017 (let ((_p46 (modulo _n16 3))) (let ((__t118 (= _p46 0))) (if __t118 __t118 (let ((_p47 (modulo _n16 5))) (let ((__t219 (= _p47 0))) (if __t219 __t219 (let ((_p48 (modulo _n16 7))) (let ((__t320 (= _p48 0))) (if __t320 __t320 (let ((_p49 (modulo _n16 11))) (let ((__t421 (= _p49 0))) (if __t421 __t421 (let ((_p50 (modulo _n16 13))) (let ((__t522 (= _p50 0))) (if __t522 __t522 (let ((_p51 (modulo _n16 17))) (let ((__t623 (= _p51 0))) (if __t623 __t623 (let ((_p52 (modulo _n16 19))) (let ((__t724 (= _p52 0))) (if __t724 __t724 (let ((_p53 (modulo _n16 23))) (= _p53 0))))))))))))))))))))))))))))) (letrec ((_is-fermat-prime?25 (lambda (_n26 _iterations27) (let ((__t828 (<= _iterations27 0))) (if __t828 __t828 (let ((_p54 (log _n26))) (let ((_p55 (log 2))) (let ((_p56 (/ _p54 _p55))) (let ((_byte-size29 (ceiling _p56))) (let ((_a30 (random _byte-size29))) (let ((_p57 (- _n26 1))) (let ((_p58 (_modulo-power11 _a30 _p57 _n26))) (let ((_p59 (= _p58 1))) (if _p59 (let ((_p60 (- _iterations27 1))) (_is-fermat-prime?25 _n26 _p60)) #f)))))))))))))) (letrec ((_generate-fermat-prime31 (lambda (_byte-size32 _iterations33) (let ((_n34 (random _byte-size32))) (let ((_p61 (_is-trivial-composite?15 _n34))) (let ((_p62 (not _p61))) (let ((_p63 (if _p62 (_is-fermat-prime?25 _n34 _iterations33) #f))) (if _p63 _n34 (_generate-fermat-prime31 _byte-size32 _iterations33))))))))) (let ((_iterations35 10)) (let ((_byte-size36 15)) (_generate-fermat-prime31 _byte-size36 _iterations35))))))))";
  ()
