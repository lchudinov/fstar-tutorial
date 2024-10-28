module Part1.Poly

// The type system of F* is called a Pure Type System or PTS.
// In F* types have types, too. Functions can take types as arguments and return types as results.

// Polymorphic identity function
let id : a:Type -> a -> a = fun a x -> x

// The same
let id1 (a:Type) (x:a) : a = x

let _ : bool = id bool true
let _ : bool = id bool false
let _ : int = id int (-1)
let _ : nat = id nat 17
let _ : string = id string "hello"
let _ : int -> int = id (int -> int) (id int)

// Type Inference

// we could replace the first type argument with an underscore
let _ : bool = id _ true
let _ : bool = id _ false
let _ : int = id _ (-1)
let _ : nat = id _ 17
let _ : string = id _ "hello"
let _ : int -> int = id _ (id _)

// Implicit arguments

// Decorating the first argument `a` with `#`, we indicate that it is an implicit argument.
let id2 (#a: Type) (x:a) : a = x

let _ : bool = id2 true
let _ : bool = id2 false
let _ : int = id2 (-1)
let _ : nat = id2 17
let _ : string = id2 "hello"
let _ : int -> int = id2 id2

// In some cases, we provide the first argument explicitly, by preciding it with a `#` sign
let _ = id2 #nat 0
let _ = id2 #(x:int{x == 0}) 0
let _ = id2 #(x:int{x <> 1}) 0
