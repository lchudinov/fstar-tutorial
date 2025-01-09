module Part2.Universes

#push-options "--print_universes"


// # Universes

let ty : Type = Type // ty: Type u#(1 + _)

// ## Basics

(*
k ::= 0 | 1 | 2 | ...
l ::= k
    | l + k | k + l
    | max l1 l2
    | a | b | c
*)

let ty0 : Type u#1 = Type u#0
let ty0' : Type u#1 = Type0
let ty1 : Type u#2 = Type u#1
let ty2 : Type u#3 = Type u#2

// let ty_bad : Type u#0 = Type u#0 // Expected expression of type Type0 got expression Type0 of type Type u#1

let ty_poly : Type u#(a + 1) = Type u#a

let _ = assert (ty_poly u#0 == ty0)
let _ = assert (ty_poly u#1 == ty1)
let _ = assert (ty_poly u#2 == ty2)

// ## Universe computations for other types

// Every type in F* lives in a particular universe. For example, here are some common types in Type u#0.

// let _ : Type0 = nat
// let _ : Type0 = bool
// let _ : Type0 = nat -> bool

let id_t : Type u#(i + 1) = a:Type u#i -> a -> a
let id : id_t = fun a x -> x

let seemingly_self_application : id_t = id _ id

let stratified_application : id_t u#i = id u#(i + 1) (id_t u#i) (id u#i)

// ## The list type

type list (a:Type u#a) : Type u#a  =
 | Nil : list a
 | Cons : hd:a -> tl:list a -> list a
 
// # The pair type
// The pair type below is parameterized by a:Type u#a and b:Type u#b and constructs a type in u#(max a b).

type pair (a:Type u#a) (b:Type u#b) : Type u#(max a b) =
  | Pair : fst:a -> snd:b -> pair a b

// # The top type

// The top type below packages a value at any type a:Type u#a with its type.

noeq
type top : Type u#(a + 1) =
  | Top : a:Type u#a -> v:a -> top

// # Russell's Paradox

assume val lower ([@@@strictly_positive] a:Type u#a) : Type u#0
assume val inject (#a: Type u#a) (x:a) : lower a
assume val project (#a:Type u#a) (x:lower a) : a
assume
val inj_proj (#a:Type u#a) (x:a)
  : Lemma (project (inject x) == x)
  
// ## Encoding Russell’s Paradox

open FStar.Squash

noeq
type _set : Type u#1 =
  | Set : x:Type0 -> f:(x -> set) -> _set
and set : Type0 = lower _set

let zero : set = inject (Set False (fun _ -> false_elim()))
let one : set = inject (Set True (fun _ -> zero))
let two : set = inject (Set bool (fun b -> if b then zero else one))

let mem (a:set) (b:set) : Type0 =
  (v:(project b).x & (a == (project b).f v))

let not_mem (a:set) (b:set) : Type0 = mem a b -> False

let delta_big = Set (s:set & not_mem s s) dfst
let delta : set = inject delta_big

let x_in_delta_x_not_in_delta (x:set) (mem_x_delta:mem x delta)
  : not_mem x x 
  = let (| v, r |) = mem_x_delta in // mem proofs are pairs
    let v : (project delta).x = v in // whose first component is an element of delta's comprehension domain
    let r : (x == (project delta).f v) = r in //and whose second component proves that x is equal to an element in delta
    inj_proj delta_big; // we use the unsound axiom to conclude that `v` is actually the domain of delta_big
    let v : (s:set & not_mem s s) = v in //and now we can retype `v` this way
    let (| s, pf |) = v in //and unpack it into its components
    let r : (x == s) = r in //and the axiom also allows us to retype `r` this way
    let pf : not_mem x x = pf in //which lets us convert pf from `not_mem s s` to the goal
    pf //not_mem x x

let delta_not_in_delta
  : not_mem delta delta
  = fun (mem_delta_delta:mem delta delta) ->
      x_in_delta_x_not_in_delta 
          delta
          mem_delta_delta
          mem_delta_delta

let x_not_mem_x_x_mem_delta (x:set) (x_not_mem_x:x `not_mem` x)
  : x `mem` delta
  = let v : (s:set & not_mem s s) = (| x, x_not_mem_x |) in //an element of the domain set of delta_big
    inj_proj delta_big; // the unsound axiom now lets us relate it to delta
    let s : (x == (project delta).f v) = //and prove that projecting delta's comprehension and applying to v return x`
        FStar.Squash.return_squash Refl
    in
    (| v,  s |)

let delta_in_delta
  : mem delta delta
  = x_not_mem_x_x_mem_delta delta delta_not_in_delta
  
let ff : False = delta_not_in_delta delta_in_delta

// ## Refinement types, FStar.Squash, prop, and Impredicativity

// ## Raising universes and the lack of cumulativity

// ## Tips for working with universes

#push-options "--print_implicits --print_universes"

let i (#a:Type) (x:a) = x
let _ = i u#0 0, i u#1 nat, i u#2 (Type u#0)

// let no_universe_poly_locally () = 
//   let i (#a:Type) (x:a) = x in
//   let _ = i u#0 0, i u#1 nat, i u#2 (Type u#0) in
//   ()

let type_poly_locally () = 
  let i (#a:Type) (x:a) = x in
  let _ = i #unit (), i #bool true, i #nat 0 in
  ()
