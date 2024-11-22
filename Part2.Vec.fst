module Part2.Vec

// # Length-indexed Lists

// ## Even and Odd-lengthed Lists

type even (a:Type) =
  | ENil : even a
  | ECons : a -> odd a -> even a
and odd (a:Type) =
  | OCons : a -> even a -> odd a
  
let rec elength #a (e:even a)
  : n:nat { n % 2 == 0}
  = match e with
    | ENil -> 0
    | ECons _ tl -> 1 + olength tl 
and olength #a (o:odd a)
  : n:nat { n % 2 == 1}
  = let OCons _ tl = o in 1 + elength tl
  
type even_or_odd_list (a:Type) : bool -> Type =
| EONil : even_or_odd_list a true
| EOCons : a -> #b:bool -> even_or_odd_list a b -> even_or_odd_list a (not b)

let rec eo_length #a #b (l:even_or_odd_list a b)
  : Tot (n:nat {if b then n % 2 == 0 else n % 2 == 1})
        (decreases l)
= match l with
  | EONil -> 0
  | EOCons _ tl -> 1 + eo_length tl
  
// ## Vectors

