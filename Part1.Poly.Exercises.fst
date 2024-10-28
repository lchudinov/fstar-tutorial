module Part1.Poly.Exercises

val apply (a b:Type) (f:a -> b) : a -> b
let apply a b f = fun x -> f x

val compose (a b c: Type) (f: b -> c) (g: a -> b) : a -> c
let compose a b c f g = fun x -> f (g x)

val twice (a : Type) (f: a -> a) : a -> a
let twice a f x = compose a a a f f x
