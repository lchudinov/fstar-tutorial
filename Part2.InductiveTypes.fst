module Part2.InductiveTypes

// # Inductive type definitions

// Strictly positive definitions

// Consider embedding a small dynamically typed programming language within F*.
// All terms in our language have the same static type `dyn`, although at runtime values could have type
// `Bool`, `Int`, Or `Function`.

// noeq
// type dyn =
//   | Bool : bool -> dyn
//   | Int : int -> dyn
//   | Function : (dyn -> dyn) -> dyn

// the Function case is problematic because it allows circular definitions that enable constructing instances of `dyn` without actually providing any base case.
// F* rejects the definition of dyn, saying "Inductive type dyn does not satisfy the strict positivity condition".

// We can suppress the error reported by using the option `__no_positivity` and see what happens.
#push-options "--__no_positivity"
noeq
type dyn =
  | Bool : bool -> dyn
  | Int : int -> dyn
  | Function : (dyn -> dyn) -> dyn
#pop-options

// Now, having declared that `dyn` is well-formed inductive type, despite not being strictly positive,
// we can beak the soundness of F*. In particular, we can write terms and claim they are total,
// when in fact their execution will loop forever.

let loop' (f:dyn): dyn
  = match f with
    | Function g -> g f
    | _ -> f

let loop : dyn
  = loop' (Function loop')

// Such loops can also allow one to prove False (breaking soundness), as the next example shows.

#push-options "--__no_positivity"
noeq
type non_positive =
  | NP : (non_positive -> False) -> non_positive
#pop-options

let almost_false (f:non_positive)
  : False
  = let NP g = f in g f

let ff
  : False
  = almost_false (NP almost_false)
  
#push-options "--__no_positivity"
noeq
type also_non_pos (f:Type -> Type) =
  | ANP : f (also_non_pos f) -> also_non_pos f
#pop-options

let f_false
  : Type -> Type
  = fun a -> (a -> False)

let almost_false_again
  : f_false (also_non_pos f_false)
  = fun x -> let ANP h = x in h x

let ff_again
  : False
  = almost_false_again (ANP almost_false_again)

// # Strictly Positive Annotations

noeq
type free (f:([@@@ strictly_positive] _:Type -> Type))
          (a:Type)
  : Type =
  | Leaf : a -> free f a
  | Branch : f (free f a) -> free f a

let binary_tree (a:Type) = free (fun t -> t & t) a
let list_redef ([@@@strictly_positive] a:Type) = list a
let variable_branching_list a = free list_redef a
let infinite_branching_tree a = free (fun t -> nat -> t) a

// let free_bad = free (fun t -> (t -> False)) int
// Binder (t: Type) is marked strictly positive, but its use in the definition is not

// # Unused Annotations

irreducible
let ref ([@@@unused] a:Type) = nat
noeq
type linked_list (a:Type) =
  | LL : ref (a & linked_list a) -> linked_list a

noeq
type neg_unused =
  | NU : ref (neg_unused -> bool) -> neg_unused
