module Part1.GettingOffTheGround.Exercises

let incr (x:int) : int = x + 1

let incr1 (x: int) : y:int{y > x} = x + 1

// let incr2 (x:int) : nat = x + 1 // fstar is unhappy

let incr3 (x:nat) : nat = x + 1

val incr4 (x:int) : int
let incr4 x = x + 1

let incr5 (x:int{x >= 0}): nat = x + 1
let incr6 (x:int{x >= 0}): y:nat{y = x + 1} = x + 1


// Computing the maximum of two integers
// Provide an implementation of the following signature:

val max (x:int) (y:int) : int
let max x y = if x >= y then x else y

val max1 (x:int) (y:int) : (z:int{(z = x \/ z = y) /\ z >= x /\ z >= y})
let max1 x y = if x >= y then x else y

val max2 (x:int) (y:int) : (z:int{z = max x y})
let max2 x y = if x > y then x else y


// Factorial

open FStar.Mul
let rec factorial (n:nat)
  : nat
  = if n = 0
    then 1
    else n * factorial (n - 1)

// Can you write down some more types for factorial?

let rec factorial2 (n:nat{n >= 0})
  : y:nat{y >= 1}
  = if n = 0
    then 1
    else n * factorial2 (n - 1)

// Fibonacci

let rec fibonacci (n:nat)
  : nat
  = if n <= 1
    then 1
    else fibonacci (n - 1) + fibonacci (n - 2)

// What other types can you give to it?
let rec fibonacci2 (n:nat{n >= 0})
  : y:nat{y >= 1}
  = if n <= 1
    then 1
    else fibonacci2 (n - 1) + fibonacci2 (n - 2)
