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

type vec (a:Type) : nat -> Type =
  | Nil: vec a 0
  | Cons: #n:nat -> hd:a -> tl:vec a n -> vec a (n + 1)
  
// ## Getting an element from a vector

let rec get #a #n (i:nat{i < n}) (v:vec a n)
  : a
  = match v with 
    | Nil -> false_elim()
    | Cons hd tl ->
      if i = 0 then hd
      else get (i - 1) tl

let rec get' #a #n (i:nat{i < n}) (v:vec a n)
  : a
  = match v with 
    | Cons hd tl ->
      if i = 0 then hd
      else get' (i - 1) tl
      
// # Exercises

// ## Exercise: Concatenating vectors

let rec append (#a:Type) (#n #m:nat) (v1:vec a n) (v2:vec a m)
  : vec a (n + m)
  = match v1 with
    | Nil -> v2
    | Cons hd tl -> append tl (Cons hd v2)
    
// ## Exercise: Splitting a vector

let rec split_at #a #n (i:nat {i <= n}) (v:vec a n) 
  : vec a i & vec a (n - i)
  = if i = 0 then Nil, v
    else let Cons hd tl = v in 
         let first, second = split_at (i - 1) tl in
         Cons hd first, second

let rec reverse #a #n (v:vec a n)
  : vec a n
  = match v with
    | Nil -> Nil
    | Cons hd tl -> append (reverse tl) (Cons hd Nil)
    
let split_at_tail #a #n (i:nat{i <= n}) (v:vec a n)
  : vec a i & vec a (n - i)
  = let rec aux (j:nat{j <= i})
                (v:vec a (n - (i - j)))
                (out:vec a (i - j))
      : vec a i & vec a (n - i)
      = if j = 0
        then reverse out, v
        else let Cons hd tl = v in
             aux (j - 1) tl (Cons hd out)
    in
    aux i v Nil
    
// ## Vectors: Probably not worth it
// See Part2.Vec.LList.fst

