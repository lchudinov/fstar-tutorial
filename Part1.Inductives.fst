module Part1.Inductives

// # Inductive types and pattern matching

// ## Enumerations
type three =
  | One_of_three : three
  | Two_of_three : three
  | Three_of_three : three

// In this case, we don't have to write the type of each constructor repeteadly.
// type three =
//   | One_of_three
//   | Two_of_three
//   | Three_of_three
  
// The name of a constructor must begin with an uppercase letter.

// F* can prove that they are distinct and they are the only terms of type `tree`.
let distinct = assert (One_of_three <> Two_of_three /\
                       Two_of_three <> Three_of_three /\
                       Three_of_three <> One_of_three)

let exhaustive (x:three) = assert (x = One_of_three \/ x = Two_of_three \/ x = Three_of_three)

let is_one (x:three)
  : bool
  = match x with
    | One_of_three -> true
    | _ -> false

let is_two (x:three)
  : bool
  = match x with
    | Two_of_three -> true
    | _ -> false

let is_three (x:three)
  : bool
  = match x with
    | Three_of_three -> true
    | _ -> false

// ## Discriminators

let three_as_int (x:three)
  : int
  = if is_one x then 1
    else if is_two x then 2
    else 3

let three_as_int' (x:three)
  : int
  = if One_of_three? x then 1
    else if Two_of_three? x then 2
    else 3
    
// For every constructor `T`, F* generates a function `T?` - a discriminator - which tests if `a:t` matches `T`.

// ## Exhaustiveness

let three_as_int'' (x:three)
  : int
  = match x with
  | One_of_three -> 1
  | Two_of_three -> 2
  | Three_of_three -> 3

// Every time use you a `match`, F* will make sure to prove you're handling all possible cases.

let only_two_as_int (x:three { not (Three_of_three? x) })
  : int
  = match x with
  | One_of_three -> 1
  | Two_of_three -> 2

// The refinement on the argument allows F* to prove that the `Three_of_three` case isn't required, since the branch is unreacheble.

// ## Tuples

type tup2 (a:Type) (b:Type) =
  | Tup2 : fst:a -> snd:b -> tup2 a b
  
type tup3 a b c =
  | Tup3 : fst:a -> snd:b -> thd:c -> tup3 a b c
  
let tup2_fst #a #b (x:tup2 a b)
  : a
  = match x with
  | Tup2 fst _ -> fst
  
let tup2_snd #a #b (x:tup2 a b)
  : b
  = match x with
  | Tup2 _ snd -> snd
  
let tup3_fst #a #b #c (x:tup3 a b c)
  : a
  = match x with
  | Tup3 fst _ _ -> fst

let tup3_snd #a #b #c (x:tup3 a b c)
  : b
  = match x with
  | Tup3 _ snd _ -> snd

let tup3_thd #a #b #c (x:tup3 a b c)
  : c
  = match x with
  | Tup3 _ _ thd -> thd
  
// ## Projectors

// F* auto-generates functions (projectors) that return components of any data contructor, for example:
// - `Tup2?.fst`, `Tup2?.snd`  
// - `Tup3?.fst`, `Tup3?.snd`, `Tup3?.thd`

// ## Syntax for tuples

// The module `FStar.Pervasives.Native.fst` defines tuples up to arity 14.
// The tuples types in `FStar.Pervasives.Native` come with sintactic sugar:

// You can write `a & b` instead of the `tup2 a b`; `a & b & c` instead of `tup3 a b c` and so on. 
// You can write `x, y` instead of the `Tup2 x y`; `x, y, z` instead of `Tup3 x y z` and so on. 
// You can write `x._1`, `x._2`, `x._3` to project the field `i` of the tuple.

// ## Records 

type point3D = {x:int; y:int; z:int }
let origin = { y=0; x=0; z=0 }

open FStar.Mul
let dot  (p0 p1:point3D) = p0.x * p1.x + p0.y * p1.y + p0.z * p1.z

let translate_X (p:point3D) (shift:int) = {p with x = p.x + shift}

let is_origin (x:point3D) =
  match x with
  | {z=0;y=0;x=0} -> true
  | _ -> false

// ## Options

let try_divide (x y:int)
  : option int
  = if y = 0 then None else Some (x / y)
  
let divide (x:int) (y:int{y<>0}) = x / y

// ## Unions, or the either type

// `Fstar.Pervasives` defines the `either` type:
type either a b =
  | Inl : v: a -> either a b
  | Inr : v: b -> either a b

let same_case #a #b #c #d (x: either a b) (y: either c d)
  : bool
  = match x, y with
  | Inl _, Inl _
  | Inr _, Inr _ -> true
  | _ -> false

let sum (x: either bool int) (y: either bool int{same_case x y})
  : z:either bool int{ Inl? z <==> Inl? x}
  = match x, y with
  | Inl xl, Inl yl -> Inl (xl || yl)
  | Inr xr, Inr yr -> Inr (xr + yr)
  
// ## Lists

// Here's the definition of `list` from `Prims`:
type list' a =
  | Nil' : list' a
  | Cons': hd:a -> tl:list' a -> list' a

// # Length of a list

let rec length #a (l:list a)
  : nat
  = match l with
  | Nil -> 0
  | _ :: tl -> 1 + length tl
  
// ## Exercises

val append (#a:Type) (l1 l2: list a) : l:list a {length l1 + length l2 = length l}
let rec append #a l1 l2
  : list a
  = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2