module Part1.PropAssertions

// 17 : x:int{x >= 0} -> (x >= 0)[17/x] -> true

// quantified formulas
// forall (x1:t1) ... (xn:tn) . p
// exists (x1:t1) ... (xn:tn) . p

// p /\ q
// p \/ q
// ~p
// p ==> q
// p <==> q

// forall (x:nat) (y: nat). x % y = 0 ==> (exists (z:nat). x = z * y)

// Propositional connectives

// val factorial (n:nat) : x:nat{x > 0}

// forall (n:nat). factorial n > 0
// exists (n:nat). factorial n > n * n

// Quantifiers

// forall (x1:t1) ... (xn:tn) . p
// exists (x1:t1) ... (xn:tn) . p

// forall (n:nat) (p: (x:nat{x >= n} -> prop)). p n

// Conjunction, Disjunction, Negation, Implication
// They are defined for propositions

// Negation `~p`, it is similar to the boolean operator `not`, but allpies to propositions rather than booleans.
// Conjunction `p /\ q` it is similar to the boolean operator `&&`, but allpies to propositions rather than booleans.
// Disjunction `p \/ q` it is similar to the boolean operator `||`, but allpies to propositions rather than booleans.
// Implication `p ==> q`
// Double implication `p <==> q`

// Atomic propositions

// `False` - Falsehood - is always invalid.
// `True` - Truth - is always valid.

// Propositional Equality

// val ( == ) (#a:Type) (x:a) (y:b) : prop

// Turning a Boolean into a proposition

// for any boolean `b`, the term `b == true` is a `prop`.
// F* automatically inserts a `b == true` if you're using `b:bool` in a context where a `prop` was expected.

// Assertions

// let sqr_is_nat (x:nat) : unit = assert (x * x >= 0)

let max x y = if x > y then x else y
let _ = assert(max 0 1 = 1)
let _ = assert(forall x y. max x y >= x /\ max x y >= y /\ (max x y = x || max x y = y))

// Assumptions

// The dual of an asserttion is an assumption. Rather than asking F* and Z3 to prove a fact,
// an assumption allows one to tell F* and Z3 to accept that some proposition is valid.

// let sqr_is_pos (x:int) = assume (x <> 0); assert(x * x > 0)
// the type of assume p is unit

// The `admit` is more powerful form of assumption. The term `admin()` can given any type you like.
let sqr_is_pos (x:int) : y:nat{y > 0} = admit()

// Both `assume` and `admit` can be helpful when you're working through a proof,
// but a proof isn't done until it's free of them.

