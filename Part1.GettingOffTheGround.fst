module Part1.GettingOffTheGround
open FStar.Mul


let empty = x:int { false } //the empty set
let zero = x:int{ x = 0 } //the type containing one element `0`
let pos = x:int { x > 0 } //the positive numbers
let neg = x:int { x < 0 } //the negative numbers
let even = x:int { x % 2 = 0 } //the even numbers
let odd = x:int { x % 2 = 1 } //the odd numbers

let incr = fun (x:int) -> x + 1
let incr2 (x:int) = x + 1
let incr3 x = x + 1
let incr4 (x:int) : int = x + 1
let more_than_twice (x:int) (y:int) : bool = x > y + y

let incr5 = fun (x:int) -> (x + 1 <: int) // `<: int` means the expected type of the expression `x + 1` is `int`. It's called a type ascription

// Recursive function. They are always named
let rec factorial (n:nat) : nat
  = if n = 0 then 1 else n * factorial (n - 1)
  
// Arrow types

val (+) : x:int -> y:int -> int

// val (+) : int -> int -> int

val (/) : int -> (divisor:int {divisor <> 0}) -> int

val incr6 : int -> int
val incr7 : x:int -> y:int{y > x}
val incr8 : x:int -> y:int{y = x + 1}

val f1 : x:(x:int{x >= 1}) -> y:(y:int{y > x}) -> z:int{ z > x + y}
val f2 : x:int{ x >= 1 } -> y:int{ y >= x } -> z:int{ z > x + y }

// Tot annotation on the last arrow indicates that the function has no side effects
val f3 : x:int{ x >= 1 } -> y:int{ y > x } -> Tot (z:int{ z > x + y })
