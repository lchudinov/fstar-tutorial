module Part4.Div

open FStar.Mul
open FStar.List
// open FStar.Int

(* You can program a function to compute Collatz sequences
   ... though no one knows if it actually terminates for all n *)

let rec collatz (n:pos)
  : Dv (list pos)
  = if n = 1 then [n]
  else if n % 2 = 0
  then n::collatz (n / 2)
  else n::collatz (3 * n + 1)
  
// # The Dv effect(for divergence)

let rec loop () : Dv unit = loop()

// let last #a (l:list a { Cons? l }) : a = L.index l (L.length l - 1)

// let rec collatz_ends_in_one (n:pos)
//    : Dv (l:list pos { Cons? l /\ last l == 1 })
//    = if n = 1 then [n]
//      else if n % 2 = 0
//      then n::collatz_ends_in_one (n / 2)
//      else n::collatz_ends_in_one (3 * n + 1)

let rec dv_false () : Dv False = dv_false()

// # Exercise

let rec collatz_spec (n:pos) (l:list pos)
  : Tot bool (decreases l) 
  = match l with
    | [] -> false
    | hd :: tl -> 
      hd = n && (
        if hd = 1 then tl = []
        else if n%2 = 0 then collatz_spec (n/2) tl
        else collatz_spec (3*n + 1) tl
      )
// collatz' may loop forever on some inputs
// but if it completes it always returns a valid
// Collatz sequence
let rec collatz' (n:pos)
  : Dv (l:list pos { collatz_spec n l } )
  = if n = 1 then [n]
    else if n % 2 = 0
    then n::collatz' (n / 2)
    else n::collatz' (3 * n + 1)

// here's another bogus implementation that always loops
let rec collatz'' (n:pos)
  : Dv (l:list pos { collatz_spec n l } )
  = collatz'' n
  
// # Example: Untyped Lambda Calculus

let var = nat
type term = 
  | Var  : var -> term
  | Int  : int -> term
  | Lam  : term -> term
  | App  : term -> term -> term
  
let rec subst (x:var) (v:term) (t:term)
  : Tot term  (decreases t) = 
  match t with
  | Var y -> if x = y then v else t
  | Int _ -> t
  | Lam t -> Lam (subst (x + 1) v t)
  | App t0 t1 -> App (subst x v t0) (subst x v t1)
  
(* This interpreter can (intentionally) loop infinitely *)
let rec interpret (t:term)
  : Dv (option term)
  = match t with
    | Var _
    | Int _
    | Lam _ -> Some t
    | App t0 t1 ->
      let head = interpret t0 in
      match head with
      | None -> None
      | Some (Lam body) -> interpret (subst 0 t1 body)
      | _ -> None //type error, expected a function

(* (\x. x x) (\x. x x) *)
let loops () : Dv _ = interpret (App (Lam (App (Var 0) (Var 0)))
                                     (Lam (App (Var 0) (Var 0))))
                                     
let rec closed' (t:term) (offset:int) 
  : bool
  = match t with
    | Int _ -> true
    | Var i -> i <= offset
    | Lam t -> closed' t (offset + 1)
    | App t0 t1 -> closed' t0 offset && closed' t1 offset
let closed t = closed' t (-1)

let rec subst' (x:var) (v:term {closed v}) (t:term)
  : Tot term  (decreases t) = 
  match t with
  | Var y -> if x = y then v else t
  | Int _ -> t
  | Lam t -> Lam (subst' (x + 1) v t)
  | App t0 t1 -> App (subst' x v t0) (subst' x v t1)
  
// # Denoting Lambda Terms into an F* Recursive Type

noeq
type dyn =
  | DErr : string -> dyn
  | DInt : int -> dyn
  | DFun : (dyn -> Dv dyn) -> dyn
  
let ctx_t = nat -> dyn

let shift (ctx: ctx_t) (v:dyn)
  : ctx_t
  = fun n -> if n = 0 then v else ctx (n - 1)

let rec denote (t: term) (ctx:ctx_t)
  : Dv dyn
  = match t with
    | Var v -> ctx v
    | Int i -> DInt i
    | Lam t -> DFun (fun v -> denote t (shift ctx v))
    | App t0 t1 ->
      match denote t0 ctx with
      | DFun f -> f (denote t1 ctx)
      | DErr msg -> DErr msg
      | DInt _ -> DErr "Cannot apply an integer"

let ctx_t' (i:int) = x:nat{x <= i} -> dyn

let shift' #i (ctx: ctx_t' i) (v:dyn)
  : ctx_t' (i + 1)
  = fun n -> if n = 0 then v else ctx (n - 1)

let max (x y: int) : int = if x < y then y else x

let rec free (t:term)
  : int
  = match t with
    | Var x -> x
    | Int _ -> -1
    | Lam t -> free t - 1
    | App t0 t1 -> max (free t0) (free t1)
    
let rec denote' (t:term) (ctx: ctx_t' (free t))
  : Dv dyn
  = match t with
    | Var v -> ctx v
    | Int i -> DInt i
    | Lam t -> DFun (fun v -> denote' t (shift' ctx v))
    | App t0 t1 ->
      match denote' t0 ctx with
      | DFun f -> f (denote' t1 ctx)
      | DErr msg -> DErr msg
      | DInt _ -> DErr "Cannot apply an integer"

let empty_context : ctx_t' (-1) = fun _ -> false_elim ()

let closed'' t = free t = -1
let denote_closed (t:term { closed'' t }) 
  : Dv dyn
  = denote' t empty_context
  
// # Shallowly Embedded Dynamically Typed Programming

(* Lifting operations on integers to operations on dyn *)

let lift (op: int -> int -> int) (n m: dyn) : dyn
  = match n, m with
  | DInt i, DInt j -> DInt (op i j)
  | _ -> DErr "Expected integers"

let mul = lift op_Multiply
let sub = lift op_Subtraction
let add = lift op_Addition
let div (n m:dyn)
  = match n, m with
    | DInt i, DInt j ->
      if j = 0 then DErr "Division by zero"
      else DInt (i % j)
    | _ -> DErr "Expected integers"

(* Branching *)
let if_ (d:dyn) (then_ else_:dyn) =
  match d with
  | DInt b -> 
    if b<>0 then then_ else else_
  | _ -> DErr "Can only branch on integers"

(* comparison *)
let eq_ (d:dyn) (d':dyn)
  : dyn 
  = match d, d' with
    | DInt i, DInt j -> DInt (if i = j then 1 else 0)
    | _ -> DErr "Can only compare integers"
    
(* Dynamically typed application *)
let app (f:dyn) (x:dyn)
  : Dv dyn
  = match f with
    | DFun f -> f x
    | _ -> DErr "Can only apply a function"
(* general recursion *)
let rec fix (f: (dyn -> Dv dyn) -> dyn -> Dv dyn) (n:dyn)
  : Dv dyn
  = f (fix f) n
  
let rec fix_alt (f: (dyn -> Dv dyn) -> dyn -> Dv dyn) 
  : Dv (dyn -> Dv dyn)
  = f (fix_alt f)

(* shorthands *)
let i (i:int) : dyn = DInt i
let lam (f:dyn -> Dv dyn) : dyn = DFun f
(* a dynamically typed analog of collatz *)
// let collatz_dyn 
//   : dyn 
//   = lam (fix (fun collatz n ->
//                 if_ (eq_ n (i 1))
//                     (i 1)
//                     (if_ (eq_ (mod n (i 2)) (i 0))
//                          (collatz (div n (i 2)))
//                          (collatz (add (mul n (i 3)) (i 1))))))