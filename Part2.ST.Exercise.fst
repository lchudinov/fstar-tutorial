module Part2.ST.Exercise

// Make st parametric in the state, i.e.,
//   st s a = s -> a & s
// And redefined all the functions below to use it
let st s a = s -> a & s

let read #s
  : st s s
  = fun s -> s, s

let write #s (s1:s)
  : st s unit
  = fun _ -> (), s1

let bind #s #a #b
         (f: st s a)
         (g: a -> st s b)
  : st s b
  = fun s0 ->
      let x, s1 = f s0 in
      g x s1

let return #s #a (x:a)
  : st s a
  = fun s -> x, s


let feq #a #b (f g : a -> b) = forall x. f x == g x
let left_identity #s #a #b (x:a) (g: a -> st s b)
  : Lemma ((v <-- return x; g v) `feq` g x)
  = ()
let right_identity #s #a (f:st s a)
  : Lemma ((x <-- f; return x) `feq` f)
  = ()
let associativity #s #a #b #c (f1:st s a) (f2:a -> st s b) (f3:b -> st s c)
  : Lemma ((x <-- f1; y <-- f2 x; f3 y) `feq`
           (y <-- (x <-- f1; f2 x); f3 y))
  = ()

let redundant_read_elim ()
  : Lemma ((read;; read) `feq` read)
  = ()

let redundant_write_elim (x y:int)
  : Lemma ((write x ;; write y) `feq` write y)
  = ()

let read_write_noop ()
  : Lemma ((x <-- read;  write x) `feq` return ())
  = ()