open Utils

(** Parameters *)
let param_gc = ref false
let param_memo = ref false

let speclist = [
  "-gc", Arg.Set param_gc, "Garbage collection";
  "-memo", Arg.Set param_memo, "Self-adjusting memoization";
]

let usage = "usage: " ^ Sys.argv.(0) ^ " [params]"

let parse_args () =
  Arg.parse speclist (fun x -> failwith ("Invalid argument: " ^ x)) usage

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
  | Set of var * exp

let primitives = ["*"; "/"; "+"; "-"; "="; "<="; ">="; "<"; ">";
                  "not"; "random"; "modulo"; "ceiling"; "even?"; "odd?"; "log"]

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
  | Set (v, exp) ->
    Printf.sprintf "(set! %s %s)"
      v (string_of_exp exp)

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
    | `List [`Atom "set!"; `Atom var; exp] ->
      Set (var, aux exp)
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
  let to_string (a, x) = Printf.sprintf "@%s%d" x a
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
    | _, _ -> failwith (Printf.sprintf "Invalid arithmetic arguments to %s: %s, %s"
                          name (to_string x) (to_string y))

  let arith1_float name f x = match x with
    | `Int n -> `Int (int_of_float (float_of_int n))
    | _ -> failwith (Printf.sprintf "Invalid arithmetic argument to %s: %s"
                       name (to_string x))

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
    | "not" -> begin function
        | [arg] -> begin match arg with
            | `Bool false -> `Bool true
            | _ -> `Bool false
          end
        | _ -> failwith "Invalid number of arguments for not"
      end
    | "random" -> fun _ -> (`Int (Random.int max_int))
    | "modulo" -> begin function
      | [x; y] -> arith "modulo" (mod) x y
      | _ -> failwith "Invalid number of arguments for modulo"
      end
    | "ceiling" -> begin function
        | [arg] -> arith1_float "ceiling" ceil arg
        | _ -> failwith "Invalid number of arguments for ceiling"
      end
    | "even?" | "odd?" -> begin function
        | [arg] -> begin match arg with
            | `Int n -> `Bool (if n mod 2 == 0 then name = "even" else name = "odd")
            | _ -> failwith ("Invalid argument for " ^ name)
          end
        | _ -> failwith ("Invalid number of arguments for " ^ name)
      end
    | "log" -> begin function
        | [arg] -> arith1_float "log" log arg
        | _ -> failwith "Invalid number of arguments for log"
      end
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
  module ASet : Set.S with type elt = A.t
  val empty : t
  val contains : t -> A.t -> bool
  val lookup : t -> A.t -> Lattice.t
  val join : t -> A.t -> Lattice.t -> t
  val compare : t -> t -> int
  val restrict : t -> ASet.t -> t
end = functor (A : AddressSignature) ->
struct
  module M = Map.Make(A)
  module ASet = Set.Make(A)
  type t = Lattice.t M.t
  let empty = M.empty
  let contains store a = M.mem a store
  let lookup store a = try M.find a store with
    | Not_found -> failwith (Printf.sprintf "Value not found at address: %s" (A.to_string a))
  let join store a v =
    if contains store a then
      M.add a (Lattice.join v (M.find a store)) store
    else
      M.add a v store
  let compare = M.compare Lattice.compare
  let restrict store addrs =
    M.filter (fun a v ->
        if ASet.mem a addrs then
          true
        else if List.exists (function
            | `Primitive _ -> true
            | _ -> false) (Lattice.conc v) then
          (* Non-primitive values could also be removed *)
          true
        else
          (* let () = Printf.printf "reclaim(%s)\n%!" (A.to_string a) in *)
          false) store
end

module Store = MakeStore(Address)
module AddressSet = Store.ASet

(** Contexts *)
module Context = struct
  type t = {
    lam : lam;
    env : Env.t;
    vals : Lattice.t list;
    store : Store.t;
  }
  let compare ctx ctx' =
    order_concat [lazy (Pervasives.compare ctx.lam ctx'.lam);
                  lazy (Env.compare ctx.env ctx'.env);
                  lazy (compare_list Lattice.compare ctx.vals ctx'.vals);
                  lazy (Store.compare ctx.store ctx'.store)]
  let hash = Hashtbl.hash
  let create lam env vals store = {lam; env; vals; store}
  let to_string ctx =
    Printf.sprintf "ctx(%s, %s)" (Value.to_string (`Closure (ctx.lam, ctx.env)))
      (string_of_list Lattice.to_string ctx.vals)
end

(** Proc Ids *)
module ProcId = struct
  type t = lam * Env.t
  let compare (lam, env) (lam', env') =
    order_concat [lazy (Pervasives.compare lam lam');
                  lazy (Env.compare env env')]
end

module ProcIdSet = Set.Make(ProcId)

(** Helper functions for the GC *)
module GCHelper = struct
  let rec fv = function
    | Var v -> StringSet.singleton v
    | Int _ | Bool _ -> StringSet.empty
    | App (f, args) ->
      List.fold_left (fun acc arg -> StringSet.union acc (fv arg)) (fv f) args
    | Abs (args, exp) ->
      StringSet.diff (fv exp) (StringSet.of_list args)
    | Letrec (v, exp, body) ->
      StringSet.remove v (StringSet.union (fv exp) (fv body))
    | If (cond, cons, alt) ->
      fv cond |> StringSet.union (fv cons) |> StringSet.union (fv alt)
    | Set (v, exp) ->
      StringSet.add v (fv exp)

  let reachable_from_vars vars env =
    StringSet.fold (fun var acc -> AddressSet.add (Env.lookup env var) acc)
      vars AddressSet.empty

  let reachable exp env =
    reachable_from_vars (fv exp) env

  let reachable_from_val v =
    List.fold_left (fun acc -> function
        | `Closure ((args, exp), env) ->
          AddressSet.union acc (reachable_from_vars (fv (Abs (args, exp))) env)
        | _ -> acc)
      AddressSet.empty (Lattice.conc v)
end

(** Frames *)
module Frame = struct
  type t =
    | AppL of exp list * Env.t
    | AppR of exp list * Lattice.t * Lattice.t list * Env.t
    | Letrec of string * Address.t * exp * Env.t
    | If of exp * exp * Env.t
    | Set of string * Env.t
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
    | If _, _ -> 1 | _, If _ -> -1
    | Set (var, env), Set (var', env') ->
      order_concat [lazy (Pervasives.compare var var');
                    lazy (Env.compare env env')]
  let to_string = function
    | AppL (exps, _) -> Printf.sprintf "AppL(%s)" (string_of_list string_of_exp exps)
    | AppR (exps, _, _, _) -> Printf.sprintf "AppR(%s)" (string_of_list string_of_exp exps)
    | Letrec (name, _, _, _) -> Printf.sprintf "Letrec(%s)" name
    | If (_, _, _) -> "If"
    | Set (v, _) -> Printf.sprintf "Set(%s)" v

  let reachable = function
    | AppL (exps, env) ->
      List.fold_left (fun acc exp ->
          AddressSet.union acc (GCHelper.reachable exp env))
        AddressSet.empty exps
    | AppR (exps, f, args, env) ->
      let r = List.fold_left (fun acc exp ->
          AddressSet.union acc (GCHelper.reachable exp env))
          AddressSet.empty exps in
      let r' = AddressSet.union (GCHelper.reachable_from_val f) r in
      List.fold_left (fun acc v ->
          AddressSet.union (GCHelper.reachable_from_val f) acc)
        r' args
    | Letrec (v, addr, exp, env) ->
      AddressSet.add addr (GCHelper.reachable exp env)
    | If (cons, alt, env) ->
      AddressSet.union (GCHelper.reachable cons env) (GCHelper.reachable alt env)
    | Set (var, env) ->
      AddressSet.singleton (Env.lookup env var)
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
  let to_string = function
    | Empty -> "KEmpty"
    | Ctx ctx -> Printf.sprintf "KCtx(%s)" (Context.to_string ctx)
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
  let to_string = string_of_list Frame.to_string
end

(** Continuation store that maps contexts to a pair of
    local continuation and and (normal) continuation *)
module KStore : sig
  type t
  val empty : t
  val lookup : t -> Context.t -> (LKont.t * Kont.t) list
  val join : t -> Context.t -> (LKont.t * Kont.t) -> t
  val compare : t -> t -> int
  val contains : t -> Context.t -> bool
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
  let contains kstore ctx = M.mem ctx kstore
end

(** Memoization-related structures *)
module Table = struct
  module LatticeList = struct
    type t = Lattice.t list
    let compare = compare_list Lattice.compare
  end
  module M = Map.Make(LatticeList)
  type t = Impure | Poly | Table of Lattice.t M.t
  let empty = Table M.empty
  let compare x y = match x, y with
  | Table x, Table y -> M.compare Lattice.compare x y
  | Table _, _ -> 1 | _, Table _ -> -1
  | _, _ -> Pervasives.compare x y
  let contains table key = match table with
    | Impure | Poly -> false
    | Table t -> M.mem key t
  let lookup table key = match table with
    | Table t -> M.find key t
    | Impure | Poly -> failwith "can't find value in memo table"
  let set table darg value = match table with
    | Impure | Poly -> table
    | Table t -> Table (M.add darg value t)
end

module Memo = struct
  module M = Map.Make(ProcId)
  type t = Table.t M.t
  let empty = M.empty
  let compare = M.compare Table.compare
  (** This is updateMemo *)
  let update memo ids =
    ProcIdSet.fold (fun id memo ->
        if M.mem id memo then
          M.add id Table.Poly memo
        else
          memo)
      ids memo
  let set_impure memo ids =
    ProcIdSet.fold (fun id memo -> M.add id Table.Impure memo) ids memo
  let contains memo id dargs =
    M.mem id memo && (Table.contains (M.find id memo) dargs)
  let lookup memo id dargs =
    Table.lookup (M.find id memo) dargs
  let set memo id darg value =
    if M.mem id memo then
      let t = M.find id memo in
      M.add id (Table.set t darg value) memo
    else
      M.add id (Table.set Table.empty darg value) memo
end

module Reads = struct
  module M = Map.Make(Address)
  module S = ProcIdSet
  type t = S.t M.t
  let empty = M.empty
  let compare = M.compare S.compare
  let update reads addrs procids =
    AddressSet.fold (fun addr reads ->
        if M.mem addr reads then
          M.add addr (S.union (M.find addr reads) procids) reads
        else
          M.add addr procids reads)
      addrs reads
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
  let reachable control env = match control with
    | Exp e -> GCHelper.reachable e env
    | Val v -> GCHelper.reachable_from_val v
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
    kstore : KStore.t;
    memo : Memo.t;
    reads : Reads.t;
  }

  let compare state state' =
    order_concat [lazy (Control.compare state.control state'.control);
                  lazy (Env.compare state.env state'.env);
                  lazy (Store.compare state.store state'.store);
                  lazy (LKont.compare state.lkont state'.lkont);
                  lazy (Kont.compare state.kont state'.kont);
                  lazy (Pervasives.compare state.time state'.time); (* TODO *)
                  lazy (KStore.compare state.kstore state'.kstore);
                  lazy (Memo.compare state.memo state'.memo);
                  lazy (Reads.compare state.reads state'.reads)]

  let to_string state = match state.control with
    | Control.Val v -> Printf.sprintf "%s" (Lattice.to_string v)
    | Control.Exp e -> Printf.sprintf "%s" (string_of_exp e)

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
    Printf.printf "%d/%d" (G.nb_vertex g) (G.nb_edges g)
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
  let alloc state x =
    (* Printf.printf "alloc(%s)\n%!" x; *)
    Address.create state.time x

  (** Injection *)
  let inject exp =
    let env, store = List.fold_left (fun (env, store) name ->
        let a = Address.create 0 name in
        (Env.extend env name a, Store.join store a (Lattice.abst (`Primitive name))))
        (Env.empty, Store.empty) primitives in
    { control = Control.Exp exp;
      env = env;
      store = store;
      lkont = LKont.empty;
      kont = Kont.Empty;
      time = 0;
      kstore = KStore.empty;
      memo = Memo.empty;
      reads = Reads.empty; }

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
  let pop lkont kont kstore memo value =
    let rec pop' lkont kont g memo = match lkont, kont with
      | [], Kont.Empty -> TripleSet.empty, memo
      | f :: lkont', k -> TripleSet.singleton (f, lkont', k), memo
      | [], Kont.Ctx ctx ->
        let memo = if !param_memo then
            Memo.set memo (ctx.Context.lam, ctx.Context.env) (ctx.Context.vals) value
          else memo in
        let (part1, g') = List.fold_left (fun (s, g') -> function
            | [], Kont.Ctx ctx when not (ContextSet.mem ctx g) ->
              (s, ContextSet.add ctx g')
            | [], Kont.Ctx _ | [], Kont.Empty -> (s, g')
            | f :: lk, k -> (TripleSet.add (f, lk, k) s, g'))
            (TripleSet.empty, ContextSet.empty) (KStore.lookup kstore ctx) in
        let gug' = ContextSet.union g g' in
        let (part2, memo) = ContextSet.fold (fun ctx' (acc, memo) ->
            let (acc', memo') = (pop' [] (Kont.Ctx ctx') gug' memo) in
            (TripleSet.union acc acc', memo'))
            g' (TripleSet.empty, memo) in
        TripleSet.union part1 part2, memo in
    pop' lkont kont ContextSet.empty memo

  (** Find all the active procedure's id *)
  let extract_procids kont kstore =
    let rec loop kont visited = match kont with
      | Kont.Empty -> ProcIdSet.empty
      | Kont.Ctx ctx ->
        if not (ContextSet.mem ctx visited) then
          let visited' = ContextSet.add ctx visited in
          List.fold_left (fun acc (lkont, kont) ->
              (* TODO: add to visited' the contexts visited in the previous call
                 to loop of this fold *)
              ProcIdSet.union acc (loop kont visited'))
            (ProcIdSet.singleton (ctx.Context.lam, ctx.Context.env))
            (KStore.lookup kstore ctx)
        else
          ProcIdSet.empty in
    loop kont ContextSet.empty

  (** Computes transitive closure of reachable relation *)
  let reachable_from root store =
    let step a = GCHelper.reachable_from_val (Store.lookup store a) in
    let rec loop todo acc =
      if AddressSet.is_empty todo then
        acc
      else
        let a = AddressSet.choose todo in
        if AddressSet.mem a acc then
          loop (AddressSet.remove a todo) acc
        else
          let addrs = step a in
          loop (AddressSet.remove a (AddressSet.union addrs todo))
            (AddressSet.add a (AddressSet.union addrs acc)) in
    loop root AddressSet.empty

  (** Computes the set of live addresses in the stack *)
  let live_stack lkont kont kstore =
    let rec visit = function
      | [] ->
        AddressSet.empty
      | frame :: lkont ->
        AddressSet.union (Frame.reachable frame) (visit lkont) in
    let rec loop kont visited =
      match kont with
      | Kont.Empty -> AddressSet.empty
      | Kont.Ctx ctx ->
        if not (ContextSet.mem ctx visited) then
          let visited' = ContextSet.add ctx visited in
          List.fold_left (fun acc (lkont, kont) ->
              (* TODO: see extract_procids *)
              (AddressSet.union acc
                 (AddressSet.union (visit lkont)
                    (loop kont visited'))))
            AddressSet.empty
            (KStore.lookup kstore ctx)
        else
          AddressSet.empty in
    AddressSet.union (visit lkont) (loop kont ContextSet.empty)

  (** Computes the set of live addresses of a state *)
  let live state =
    reachable_from (AddressSet.union (Control.reachable state.control state.env)
                      (live_stack state.lkont state.kont state.kstore))
      state.store

  (** GC *)
  let gc state =
    {state with store = Store.restrict state.store (live state)}

  (** Step a continuation state *)
  let step_kont state v frame lkont kont = match frame with
    | Frame.AppL (arg :: args, env) ->
      let lkont = LKont.push (Frame.AppR (args, v, [], state.env)) lkont in
      [{state with control = Exp arg; env; lkont; kont}]
    | Frame.AppL ([], env) ->
      failwith "TODO: functions with 0 arguments not yet implemented"
    | Frame.AppR (arg :: args, clo, argsv, env) ->
      let lkont = LKont.push (Frame.AppR (args, clo, v :: argsv, env)) lkont in
      [{state with control = Exp arg; env; lkont; kont}]
    | Frame.AppR ([], clo, args', env) ->
      let args = List.rev (v :: args') in
      List.flatten (List.map (function
          | `Closure (((xs, body), env') as closure) ->
            (* the only tricky case: we need to push the local continuation in
               the continuation store, and then replace the local cont by an
               empty one *)
            if List.length xs != List.length args then
              []
            else if !param_memo && Memo.contains state.memo closure args then
              [{state with control = Val (Memo.lookup state.memo closure args);
                           lkont; kont; time = tick state}]
            else
              let (env'', store) = List.fold_left2 (fun (env, store) x v ->
                  let a = alloc state x in
                  (Env.extend env x a,
                   Store.join store a v))
                  (env', state.store) xs args in
              let ctx = Context.create (xs, body) env' args state.store in
              (* Error in the paper: they extend the stack store with
                 (state.lkont, state.kont), therefore forgetting to remove the
                 AppR that is on top of the stack *)
              let kstore = KStore.join state.kstore ctx (lkont, state.kont) in
              [{state with control = Exp body; env = env''; store; kstore;
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
          (Lattice.conc clo))
    | Frame.Letrec (x, a, body, env) ->
      let store = Store.join state.store a v in
      [{state with control = Exp body; store; env; lkont; kont;
                   time = tick state}]
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
            []) (Lattice.conc v))
    | Frame.Set (var, env) ->
      let a = Env.lookup env var in
      let store = Store.join state.store a v in
      (* return value should be undefined but who cares *)
      [{state with control = Val v; env; lkont; kont; store; time = tick state}]

  (** Step an evaluation state *)
  let step_eval state = function
    | Var x ->
      let a = Env.lookup state.env x in
      let v = Store.lookup state.store a in
      let reads = if !param_memo then
          Reads.update state.reads (AddressSet.singleton a)
            (extract_procids state.kont state.kstore)
        else state.reads in
      [{state with control = Val v; reads; time = tick state}]
    | Int n ->
      [{state with control = Val (Lattice.abst (Value.num n)); time = tick state}]
    | Bool b ->
      [{state with control = Val (Lattice.abst (Value.bool b)); time = tick state}]
    | Abs lam ->
      let memo = if !param_memo then
          Memo.update state.memo (ProcIdSet.singleton (lam, state.env))
        else state.memo in
      [{state with control = Val (Lattice.abst (`Closure (lam, state.env)));
                   memo; time = tick state}]
    | App (f, args) ->
      let lkont = LKont.push (Frame.AppL (args, state.env)) state.lkont in
      [{state with control = Exp f; lkont; time = tick state}]
    | Letrec (x, exp, body) ->
      let a = alloc state x in
      let env = Env.extend state.env x a in
      let store = Store.join state.store a Lattice.bot in
      let lkont = LKont.push (Frame.Letrec (x, a, body, env)) state.lkont in
      [{state with control = Exp exp; env; store; lkont; time = tick state}]
    | If (cond, cons, alt) ->
      let lkont = LKont.push (Frame.If (cons, alt, state.env)) state.lkont in
      [{state with control = Exp cond; lkont; time = tick state}]
    | Set (var, exp) ->
      let lkont = LKont.push (Frame.Set (var, state.env)) state.lkont in
      let ids = extract_procids state.kont state.kstore in
      let memo = if !param_memo then
          Memo.set_impure state.memo ids
        else state.memo in
      [{state with control = Exp exp; lkont; memo; time = tick state}]

  (** Main step function *)
  let step_no_gc state = match state.control with
    | Exp exp -> step_eval state exp
    | Val v ->
      let (popped, memo) = pop state.lkont state.kont state.kstore state.memo v in
      let state = {state with memo} in
      List.flatten (List.map (fun (frame, lkont, kont) ->
          step_kont state v frame lkont kont)
          (TripleSet.elements popped))

  (** Garbage-collected step *)
  let step state = step_no_gc (if !param_gc then gc state else state)

  (** Simple work-list state space exploration *)
  let run exp =
    let rec loop visited todo graph finals =
      if StateSet.is_empty todo then
        (graph, finals)
      else
        let state = StateSet.choose todo in
        let rest = StateSet.remove state todo in
        if StateSet.mem state visited then
          loop visited rest graph finals
        else begin
          (* Printf.printf "Stepping %s: " (State.to_string state); *)
          begin match step state with
            | [] ->
              (* Printf.printf "final state\n%!"; *)
              loop (StateSet.add state visited) rest graph (state :: finals)
            | stepped ->
              (* Printf.printf "%s\n%!"
                 (String.concat ", " (List.map State.to_string stepped)); *)
              loop (StateSet.add state visited)
                (StateSet.union (StateSet.of_list stepped) rest)
                (Graph.add_transitions graph state stepped)
                finals
          end
        end in
    loop StateSet.empty (StateSet.singleton (inject exp)) Graph.empty []
end

let run name source =
  let t0 = Unix.gettimeofday () in
  let (graph, finals) = CESK.run (parse source) in
  let t1 = Unix.gettimeofday () in
  Printf.printf "%s: %s " name (String.concat "|"
                                     (List.map State.to_string finals));
  Graph.output graph (name ^ ".dot");
  Graph.output_stats graph;
  Printf.printf " %f\n%!" (t1 -. t0)

let () =
  parse_args ();
(*  run "sq" "((lambda (x) (* x x)) 8)";
  run "loopy1" "(letrec ((f (lambda (x) (f x)))) (f 1))";
  run "loopy2" "((lambda (x) (x x)) (lambda (y) (y y)))";
  run "fac" "(letrec ((fac (lambda (n) (if (= n 0) 1 (* n (fac (- n 1))))))) (fac 8))";
  run "fib" "(letrec ((fib (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))) (fib 8))";
  run "safeloopy1" "(letrec ((count (lambda (n) (letrec ((t (= n 0))) (if t 123 (letrec ((u (- n 1))) (letrec ((v (count u))) v))))))) (count 8))"; *)
  run "fac" "(letrec ((fac (lambda (n) (let ((t (= n 0))) (if t 1 (let ((u (- n 1))) (let ((v (fac u))) (* n v)))))))) (fac 10))";
  run "rotate" "(letrec ((_rotate0 (lambda (_n1 _x2 _y3 _z4) (let ((_p5 (= _n1 0))) (if _p5 _x2 (let ((_p6 (- _n1 1))) (_rotate0 _p6 _y3 _z4 _x2))))))) (_rotate0 41 5 #t #f))";
  run "gcIpdExample" "(let ((_id0 (lambda (_x1) _x1))) (letrec ((_f2 (lambda (_n3) (let ((_p6 (<= _n3 1))) (if _p6 1 (let ((_p7 (- _n3 1))) (let ((_p8 (_f2 _p7))) (* _n3 _p8)))))))) (letrec ((_g4 (lambda (_n5) (let ((_p9 (<= _n5 1))) (if _p9 1 (let ((_p10 (* _n5 _n5))) (let ((_p11 (- _n5 1))) (let ((_p12 (_g4 _p11))) (+ _p10 _p12))))))))) (let ((_p13 (_id0 _f2))) (let ((_p14 (_p13 3))) (let ((_p15 (_id0 _g4))) (let ((_p16 (_p15 4))) (+ _p14 _p16))))))))";
  run "fib" "(letrec ((_fib0 (lambda (_n1) (let ((_p2 (< _n1 2))) (if _p2 _n1 (let ((_p3 (- _n1 1))) (let ((_p4 (_fib0 _p3))) (let ((_p5 (- _n1 2))) (let ((_p6 (_fib0 _p5))) (+ _p4 _p6)))))))))) (_fib0 4))";
  run "mj09" "(let ((_h0 (lambda (_b1) (let ((_g2 (lambda (_z3) _z3))) (let ((_f4 (lambda (_k5) (if _b1 (_k5 1) (_k5 2))))) (let ((_y6 (_f4 (lambda (_x7) _x7)))) (_g2 _y6))))))) (let ((_x8 (_h0 #t))) (let ((_y9 (_h0 #f))) _y9)))";
  run "eta" "(let ((_do-something0 (lambda (x) 10))) (let ((_id1 (lambda (_y2) (let ((_tmp13 (_do-something0 1))) _y2)))) (let ((_p7 (_id1 (lambda (_a5) _a5)))) (let ((_tmp24 (_p7 #t))) (let ((_p8 (_id1 (lambda (_b6) _b6)))) (_p8 #f))))))";
  run "kcfa2" "(let ((_f10 (lambda (_x12) (let ((_f23 (lambda (_x26) (let ((_z7 (lambda (_y18 _y29) _y18))) (_z7 _x12 _x26))))) (let ((_b4 (_f23 #t))) (let ((_c5 (_f23 #f))) (_f23 #t))))))) (let ((_a1 (_f10 #t))) (_f10 #f)))";
  run "blur" "(let ((_id0 (lambda (_x1) _x1))) (let ((_blur2 (lambda (_y3) _y3))) (letrec ((_lp4 (lambda (_a5 _n6) (let ((_p9 (<= _n6 1))) (if _p9 (_id0 _a5) (let ((_p10 (_blur2 _id0))) (let ((_r7 (_p10 #t))) (let ((_p11 (_blur2 _id0))) (let ((_s8 (_p11 #f))) (let ((_p12 (_blur2 _lp4))) (let ((_p13 (- _n6 1))) (let ((_p14 (_p12 _s8 _p13))) (not _p14))))))))))))) (_lp4 #f 2))))";
  run "kcfa3" "(let ((_f10 (lambda (_x12) (let ((_f23 (lambda (_x25) (let ((_f36 (lambda (_x38) (let ((_z9 (lambda (_y110 _y211 _y312) _y110))) (_z9 _x12 _x25 _x38))))) (let ((_c7 (_f36 #t))) (_f36 #f)))))) (let ((_b4 (_f23 #t))) (_f23 #f)))))) (let ((_a1 (_f10 #t))) (_f10 #f)))";
  run "loop2" "(letrec ((_lp10 (lambda (_i1 _x2) (let ((_a3 (= 0 _i1))) (if _a3 _x2 (letrec ((_lp24 (lambda (_j5 _f6 _y7) (let ((_b8 (= 0 _j5))) (if _b8 (let ((_p10 (- _i1 1))) (_lp10 _p10 _y7)) (let ((_p11 (- _j5 1))) (let ((_p12 (_f6 _y7))) (_lp24 _p11 _f6 _p12)))))))) (_lp24 10 (lambda (_n9) (+ _n9 _i1)) _x2))))))) (_lp10 10 0))";
(*
  run "sat" "(let ((_phi5 (lambda (_x16 _x27 _x38 _x49) (let ((__t010 _x16)) (let ((_p23 (if __t010 __t010 (let ((__t111 (not _x27))) (if __t111 __t111 (not _x38)))))) (if _p23 (let ((__t212 (not _x27))) (let ((_p24 (if __t212 __t212 (not _x38)))) (if _p24 (let ((__t313 _x49)) (if __t313 __t313 _x27)) #f))) #f)))))) (let ((_try14 (lambda (_f15) (let ((__t416 (_f15 #t))) (if __t416 __t416 (_f15 #f)))))) (let ((_sat-solve-417 (lambda (_p18) (_try14 (lambda (_n119) (_try14 (lambda (_n220) (_try14 (lambda (_n321) (_try14 (lambda (_n422) (_p18 _n119 _n220 _n321 _n422)))))))))))) (_sat-solve-417 _phi5))))";
  run "primtest" "(let ((_square9 (lambda (_x10) (* _x10 _x10)))) (letrec ((_modulo-power11 (lambda (_base12 _exp13 _n14) (let ((_p37 (= _exp13 0))) (if _p37 1 (let ((_p38 (odd? _exp13))) (if _p38 (let ((_p39 (- _exp13 1))) (let ((_p40 (_modulo-power11 _base12 _p39 _n14))) (let ((_p41 (* _base12 _p40))) (modulo _p41 _n14)))) (let ((_p42 (/ _exp13 2))) (let ((_p43 (_modulo-power11 _base12 _p42 _n14))) (let ((_p44 (_square9 _p43))) (modulo _p44 _n14))))))))))) (let ((_is-trivial-composite?15 (lambda (_n16) (let ((_p45 (modulo _n16 2))) (let ((__t017 (= _p45 0))) (if __t017 __t017 (let ((_p46 (modulo _n16 3))) (let ((__t118 (= _p46 0))) (if __t118 __t118 (let ((_p47 (modulo _n16 5))) (let ((__t219 (= _p47 0))) (if __t219 __t219 (let ((_p48 (modulo _n16 7))) (let ((__t320 (= _p48 0))) (if __t320 __t320 (let ((_p49 (modulo _n16 11))) (let ((__t421 (= _p49 0))) (if __t421 __t421 (let ((_p50 (modulo _n16 13))) (let ((__t522 (= _p50 0))) (if __t522 __t522 (let ((_p51 (modulo _n16 17))) (let ((__t623 (= _p51 0))) (if __t623 __t623 (let ((_p52 (modulo _n16 19))) (let ((__t724 (= _p52 0))) (if __t724 __t724 (let ((_p53 (modulo _n16 23))) (= _p53 0))))))))))))))))))))))))))))) (letrec ((_is-fermat-prime?25 (lambda (_n26 _iterations27) (let ((__t828 (<= _iterations27 0))) (if __t828 __t828 (let ((_p54 (log _n26))) (let ((_p55 (log 2))) (let ((_p56 (/ _p54 _p55))) (let ((_byte-size29 (ceiling _p56))) (let ((_a30 (random _byte-size29))) (let ((_p57 (- _n26 1))) (let ((_p58 (_modulo-power11 _a30 _p57 _n26))) (let ((_p59 (= _p58 1))) (if _p59 (let ((_p60 (- _iterations27 1))) (_is-fermat-prime?25 _n26 _p60)) #f)))))))))))))) (letrec ((_generate-fermat-prime31 (lambda (_byte-size32 _iterations33) (let ((_n34 (random _byte-size32))) (let ((_p61 (_is-trivial-composite?15 _n34))) (let ((_p62 (not _p61))) (let ((_p63 (if _p62 (_is-fermat-prime?25 _n34 _iterations33) #f))) (if _p63 _n34 (_generate-fermat-prime31 _byte-size32 _iterations33))))))))) (let ((_iterations35 10)) (let ((_byte-size36 15)) (_generate-fermat-prime31 _byte-size36 _iterations35))))))))"; *)
  ()
