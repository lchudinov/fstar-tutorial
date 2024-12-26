module Part2.Option

let bind #a #b
         (f: option a)
         (g: a -> option b)
  : option b
  = match f with
    | Some x -> g x
    | None -> None
  
let return #a (x:a)
  : option a
  = Some x

let eq #a (f g : option a) = f == g

let left_identity #a #b (x:a) (g: a -> option b)
  : Lemma ((v <-- return x; g v) `eq` g x)
  = ()
let right_identity #a (f:option a)
  : Lemma ((x <-- f; return x) `eq` f)
  = ()
let associativity #a #b #c (f1:option a) (f2:a -> option b) (f3:b -> option c)
  : Lemma ((x <-- f1; y <-- f2 x; f3 y) `eq`
           (y <-- (x <-- f1; f2 x); f3 y))
  = ()