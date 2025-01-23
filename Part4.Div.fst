module Part4.Div

open FStar.Mul
open FStar.List

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