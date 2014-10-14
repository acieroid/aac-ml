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
end

module Address : AddressSignature = struct
  type t = int * string
  let compare = Pervasives.compare
  let create a x = (a, x)
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
    | `Bool -> true
    | _ -> false
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
    | `Bool b -> b
    | _ -> false
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
  val compare : t -> t -> int
end = struct
  module M = Map.Make(Context)
  module S = Set.Make(Kont)
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
  let tick state =
    if Value.max_addr = -1 then
      state.time + 1
    else
      (state.time + 1) mod Value.max_addr
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
      store = store;
      kont = Kont.Empty;
      time = 0;
      kstore = KStore.empty; }

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
  let step state = match state.control with
    | Exp (Var x) ->
      let v = Store.lookup state.store (Env.lookup state.env x) in
      [{state with control = Val v; time = tick state}]
    | Exp (Int n) ->
      [{state with control = Val (Lattice.abst (Value.num n)); time = tick state}]
    | Exp (Bool b) ->
      [{state with control = Val (Lattice.abst (Value.bool b)); time = tick state}]
    | Exp (Abs lam) ->
      [{state with control = Val (Lattice.abst (`Closure (lam, state.env)));
                   time = tick state}]
    | Exp (App (f, args)) ->
      let ctx = Context.create (App (f, args)) state.env state.store state.time in
      let kont = Kont.Cons (Frame.AppL (args, state.env), ctx) in
      let kstore = KStore.join state.kstore ctx state.kont in
      [{state with control = Exp f; kont; kstore; time = tick state}]
    | Exp (Letrec (x, exp, body)) ->
      let ctx = Context.create (Letrec (x, exp, body)) state.env state.store state.time in
      let a = alloc state x in
      let env = Env.extend state.env x a in
      let store = Store.join state.store a Lattice.bot in
      let kont = Kont.Cons (Frame.Letrec (x, a, body, env), ctx) in
      let kstore = KStore.join state.kstore ctx state.kont in
      [{control = Exp exp; env; store; kont; kstore; time = tick state}]
    | Exp (If (cond, cons, alt)) ->
      let ctx = Context.create (If (cond, cons, alt)) state.env state.store state.time in
      let kont = Kont.Cons (Frame.If (cons, alt, state.env), ctx) in
      let kstore = KStore.join state.kstore ctx state.kont in
      [{state with control = Exp cond; kont; kstore; time = tick state}]
    | Val v -> begin match state.kont with
        | Kont.Empty -> [] (* Evaluation finished? *)
        | Kont.Cons (Frame.AppL (arg :: args, env), ctx) ->
          let kont = Kont.Cons (Frame.AppR (args, v, [], env), ctx) in
          [{state with control = Exp arg; env; kont}]
        | Kont.Cons (Frame.AppL ([], env), ctx) ->
          failwith "TODO: functions with 0 arguments are NYI"
        | Kont.Cons (Frame.AppR (arg :: args, clo, argsv, env), ctx) ->
          let kont = Kont.Cons (Frame.AppR (args, clo, v :: argsv, env), ctx) in
          [{state with control = Exp arg; env; kont}]
        | Kont.Cons (Frame.AppR ([], clo, args', env), ctx) ->
          let args = List.rev (v :: args') in
          let konts = KStore.lookup state.kstore ctx in
          List.flatten (List.map (fun kont ->
              List.flatten
                (List.map (function
                     | `Closure ((xs, body), env') ->
                       if List.length xs != List.length args then
                         failwith (Printf.sprintf
                                     "Arity mismatch: expected %d argument, got %d"
                                     (List.length xs) (List.length args))
                       else
                         let (env'', store) = List.fold_left2 (fun (env, store) x v ->
                             let a = alloc state x in
                             (Env.extend env x a,
                              Store.join store a v))
                             (env', state.store) xs args in
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
              konts)
        | Kont.Cons (Frame.Letrec (x, a, body, env), ctx) ->
          let store = Store.join state.store a v in
          let konts = KStore.lookup state.kstore ctx in
          List.map (fun kont ->
              {state with control = Exp body; store; env; kont;
                          time = tick state})
            konts
        | Kont.Cons (Frame.If (cons, alt, env), ctx) ->
          let konts = KStore.lookup state.kstore ctx in
          List.flatten (List.map (fun kont ->
              let t = {state with control = Exp cons; env; kont; time = tick state}
              and f = {state with control = Exp alt;  env; kont; time = tick state} in
              List.flatten (List.map (fun v ->
                  if Value.is_true v || Value.is_false v then
                    [t; f]
                  else if Value.is_true v then
                    [t]
                  else if Value.is_false v then
                    [f]
                  else
                    []) (Lattice.conc v)))
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
          (* Printf.printf "Stepping %s: " (State.to_string state); *)
          begin match step state with
            | [] ->
              (* Printf.printf "final state\n%!"; *)
              loop (StateSet.add state visited) rest (state :: finals)
            | stepped ->
              (* Printf.printf "%s\n%!"
                (String.concat ", " (List.map State.to_string stepped)); *)
              loop (StateSet.add state visited)
                (StateSet.union (StateSet.of_list stepped) rest) finals
          end
        end in
    loop StateSet.empty (StateSet.singleton (inject exp)) []
end

let run name source =
  let finals = CESK.run (parse source) in
  Printf.printf "%s: %s\n%!" name (String.concat "|"
                                     (List.map State.to_string finals))


let () =
  run "add" "(+ 1 2)";
  run "simple" "(letrec ((f (lambda (x y) (if x x y)))) (f #t 3))";
  run "sq" "((lambda (x) (* x x)) 8)";
  run "loopy1" "(letrec ((f (lambda (x) (f x)))) (f 1))";
  run "loopy2" "((lambda (x) (x x)) (lambda (y) (y y)))";
  run "fac" "(letrec ((fac (lambda (n) (if (= n 0) 1 (* n (fac (- n 1))))))) (fac 8))";
  run "fib" "(letrec ((fib (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))))) (fib 8))";
  run "safeloopy1" "(letrec ((count (lambda (n) (letrec ((t (= n 0))) (if t 123 (letrec ((u (- n 1))) (letrec ((v (count u))) v))))))) (count 8))"
