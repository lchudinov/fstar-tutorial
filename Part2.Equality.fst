module Part2.Equality

// # Definitional Equality

// Terms that are related by reduction are called `definitionally equal`.
// For example, (\lambda x. x) 0 and 0 are definitionally equal, since the former reduces
// in a single step of computation to the latter.

type vec (a:Type) : nat -> Type =
  | Nil : vec a 0
  | Cons : #n:nat -> hd:a -> tl:vec a n -> vec a (n + 1)


let conv_vec_0 (#a:Type) (v:vec a ((fun x -> x) 0))
  : vec a 0
  = v

let conv_vec_1 (#a:Type) (v:vec a ((fun x -> x + 1) 0))
  : vec a 1
  = v

open FStar.Mul

let rec factorial (n:nat)
  : nat
  = if n = 0 then 1
    else n * factorial (n - 1)

let conv_vec_6 (#a:Type) (v:vec a (factorial 3))
  : vec a 6
  = v

let conv_int (x : (fun b -> if b then int else bool) true)
  : int
  = x + 1
  
// # Propositional Equality

type equals (#a:Type) : a -> a -> Type =
  | Reflexivity : #x:a -> equals x x
  
let z_equals_z
  : equals 0 0
  = Reflexivity

let fact_3_eq_6
  : equals (factorial 3) 6
  = Reflexivity #_ #6

let reflexivity #a (x:a)
  : equals x x
  = Reflexivity

let symmetry #a (x y : a) (pf:equals x y)
  : equals y x
  = Reflexivity

let transitivity #a (x y z : a) (pf1:equals x y) (pf2:equals y z)
  : equals x z
  = Reflexivity

let uip_refl #a (x y:a) (pf:equals x y)
  : equals pf (Reflexivity #a #x)
  = Reflexivity

let uip_refl_explicit #a (x y:a) (pf:equals x y)
  : equals #(equals x y) pf (Reflexivity #a #x)
  = Reflexivity #(equals x y) #(Reflexivity #a #x)

// let ( == ) #a (x y : a) = squash (equals x y)

// # Equality Reflection

// ## Implicit conversions using provable equalities

let pconv_vec_z (#a:Type) (#n:nat) (_:(n == 0)) (v:vec a n)
  : vec a 0
  = v

let pconv_vec_nm (#a:Type) (#n #m:nat) (_:(n == m)) (v:vec a n)
  : vec a m
  = v

let pconv_int (#a:Type) (_:(a == int)) (x:a)
  : int
  = x + 1

let pconv_ab (#a #b:Type) (_:(a == b)) (v:a)
  : b
  = v
  
let pconv_der (#a #b:Type)
              (x y:int)
              (h:((x > 0 ==> a == int) /\
                  (y > 0 ==> b == int) /\
                  (x > 0 \/ y > 0)))
              (aa:a)
              (bb:b)
  : int
  = if x > 0 then aa - 1 else bb + 1
  
// ## Undecidability and Weak Normalization

// # Functional Extensionality

// see file Part2.Leibniz.fst

// # Decidable equality and equality qualifiers

val ( = ) (#a:eqtype) (x y:a) : bool

let dec_equals (#a:eqtype) (x y:a) (_:squash (x = y))
  : equals x y
  = Reflexivity

let equals_dec (#a:eqtype) (x y:a) (_:equals x y)
  : squash (x = y)
  = ()
  
// 1. `noeq` instructs F* to consider that the type does not support decidable equality
noeq
type itree (a:Type) =
  | End : itree a
  | Node : hd:nat -> tl:(nat -> itree a) -> itree a
  
// 2. `unopteq`
unopteq
type t (f: Type -> Type) =
  | T : f bool -> t f

let _ = assert (hasEq (t list))

[@@expect_failure]
let _ = assert (hasEq (fun x -> x -> x))