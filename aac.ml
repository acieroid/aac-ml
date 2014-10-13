open Utils

(** The language *)
type var = string
and lam = var * exp
and exp =
  | Var of var
  | App of exp * exp
  | Abs of lam

let rec string_of_exp = function
  | Var x -> x
  | App (e0, e1) ->
    Printf.sprintf "(%s %s)" (string_of_exp e0) (string_of_exp e1)
  | Abs (x, e) ->
    Printf.sprintf "(lambda (%s) %s)" x (string_of_exp e)

(** Addresses *)
module type AddressSignature = sig
  type t
  val compare : t -> t -> int
  val create : int -> t
end

module Address : AddressSignature = struct
  type t = int
  let compare = Pervasives.compare
  let create a = a
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
module Value = struct
  type t =
    | Closure of lam * Env.t
  let compare x y = match x, y with
    | Closure (lam, env), Closure (lam', env') ->
      order_concat [lazy (Pervasives.compare lam lam');
                    lazy (Env.compare env env')]
  let to_string = function
    | Closure ((x, e), _) ->
      Printf.sprintf "(lambda (%s) %s)" x (string_of_exp e)
end

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
  let join v v' = VSet.union v v' (* TODO: use set *)
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
  | Not_found -> failwith ("Value not found")
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
    Printf.sprintf "ctx(%s, %s)" (string_of_exp ctx.exp) (string_of_int ctx.time)
end

(** Frames *)
module Frame = struct
  type t =
    | AppL of exp * Env.t
    (* typo the AAC paper in 8th extended version, Fig. 2: appR(v, ρ) *)
    | AppR of Lattice.t
  let compare x y = match x, y with
    | AppL (exp, env), AppL (exp', env') ->
      order_concat [lazy (Pervasives.compare exp exp');
                    lazy (Env.compare env env')]
    | AppL _, _ -> 1 | _, AppL _ -> -1
    | AppR v, AppR v' ->
      Lattice.compare v v'
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
  val compare : t -> t -> int
end = struct
  module M = Map.Make(Context)
  module S = Set.Make(Kont)
  type t = S.t M.t (* TODO: set *)
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
    store : Store.t;
    kont : Kont.t;
    time : int;
    kstore : KStore.t;
  }
  let compare state state' =
    order_concat [lazy (Control.compare state.control state'.control);
                  lazy (Env.compare state.env state'.env);
                  lazy (Store.compare state.store state'.store);
                  lazy (Kont.compare state.kont state'.kont);
                  lazy (Pervasives.compare state.time state'.time); (* TODO *)
                  lazy (KStore.compare state.kstore state'.kstore)]
  let inject exp = {
    control = Control.Exp exp;
    env = Env.empty;
    store = Store.empty;
    kont = Kont.Empty;
    time = 0;
    kstore = KStore.empty;
  }
  let to_string state = match state.control with
    | Control.Val v -> Lattice.to_string v
    | Control.Exp e -> string_of_exp e
end

module StateSet = Set.Make(State)

(** The CESK machine itself *)
module CESK = struct
  open State
  open Control

  (** Tick and alloc implementations *)
  let tick state = state.time + 1
  let alloc state = Address.create state.time

  (** Step function *)
  let step state = match state.control with
    | Exp (Var x) ->
      let v = Store.lookup state.store (Env.lookup state.env x) in
      [{state with control = Val v; time = tick state}]
    | Exp (Abs lam) ->
      [{state with control = Val (Lattice.abst (Value.Closure (lam, state.env)));
                   time = tick state}]
    | Exp (App (e0, e1)) ->
      let ctx = Context.create (App (e0, e1)) state.env state.store state.time in
      let kont = Kont.Cons ((Frame.AppL (e1, state.env)), ctx) in
      Printf.printf "Adding kont in kstore at %s\n" (Context.to_string ctx);
      let kstore = KStore.join state.kstore ctx state.kont in
      [{state with control = Exp e0; kont; kstore; time = tick state}]
    | Val v -> begin match state.kont with
        | Kont.Empty -> [] (* Evaluation finished? *)
        | Kont.Cons (Frame.AppL (e, env), ctx) ->
          let kont = Kont.Cons (Frame.AppR v, ctx) in
          [{state with control = Exp e; env; kont}]
        | Kont.Cons (Frame.AppR vs, ctx) ->
          Printf.printf "Looking up in kstore at %s\n" (Context.to_string ctx);
          let konts = KStore.lookup state.kstore ctx in
          List.flatten (List.map (fun kont ->
              List.map (function
                  | Value.Closure ((x, e), env') as v ->
                    let a = alloc state in
                    let env'' = Env.extend env' x a in
                    let store = Store.join state.store a (Lattice.abst v) in
                    {state with control = Exp e; env = env''; store; kont; time = tick state})
                (Lattice.conc vs))
              konts)
      end

  (** Simple work-list state space exploration *)
  let run exp =
    let rec loop visited todo finals =
      if StateSet.is_empty todo then
        finals
      else
        let state = StateSet.choose todo in
        let rest = StateSet.remove state todo in
        if StateSet.mem state visited then
          loop visited rest finals
        else begin
          Printf.printf "Stepping %s: " (State.to_string state);
          begin match step state with
            | [] ->
              Printf.printf "final state\n%!";
              loop (StateSet.add state visited) rest (state :: finals) (* final state *)
            | stepped ->
              Printf.printf "%s\n%!"
                (String.concat ", " (List.map State.to_string stepped));
              loop (StateSet.add state visited)
                (StateSet.union (StateSet.of_list stepped) rest) finals
          end
        end in
    loop StateSet.empty (StateSet.singleton (inject exp)) []
end

let () =
  let id1 = Abs ("x", (Var "x")) in
  let id2 = Abs ("y", (Var "y")) in
  let idid = (App (id1, id2)) in
  let finals = CESK.run idid in
  List.iter (fun state -> print_endline (State.to_string state)) finals
