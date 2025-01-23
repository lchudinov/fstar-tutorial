module Part4.ErasureAndGhost
open FStar.Ghost
open FStar.Mul

// # Erasure effect

noeq
type vec (a:Type) : nat -> Type =
  | Nil : vec a 0
  | Cons : #n:erased nat -> hd:a -> tl:vec a n -> vec a (n + 1)
  
let rec append #a (#n #m:erased nat) (v1:vec a n) (v2:vec a m)
  : vec a (n + m)
  = match v1 with
    | Nil -> v2
    | Cons hd tl -> Cons hd (append tl v2)
    
let rec list_append #a (l1 l2:list a) =
    match l1 with
    | [] -> []
    | hd::tl -> hd :: list_append tl l2
    
// # Ghost: A Primitive Effect


let rec factorial (n:nat)
  : GTot nat
  = if n = 0 then 1 else n * factorial (n - 1)
  
let rec factorial_tail (n:nat) (out:nat)
  : Tot (r:nat { r == out * factorial n })
  = if n = 0 then out
    else factorial_tail (n - 1) (n * out)

let fact (n:nat) 
  : Tot (r:nat { r == factorial n })
  = factorial_tail n 1

// # Erasable and Non-informative Types

noeq
type vec' a : nat -> Type = 
  | Nil' : vec' a 0
  | Cons' : #n:erased nat -> hd:a -> tl:vec' a (reveal n) -> vec' a (reveal n + 1)

let rec append' #a (#n #m:erased nat) (v0:vec' a (reveal n)) (v1:vec' a (reveal m))
  : Tot (vec' a (reveal n + reveal m))
        (decreases (reveal n))
  = match v0 with   
    | Nil' -> v1
    | Cons' #_ #n_tl hd tl ->
      Cons' #a 
           #(hide (reveal n_tl + reveal m))
           hd 
           (append' #a 
                   #n_tl
                   #m
                   tl
                   v1)
