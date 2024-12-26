module Part2.ST

// # A First Model of Computational Effects

// ## A First Taste: The State Monad

// consider a program that manipulates a single piece of mutable state, just a single integer that programs 
// can read and write, and which returns a result of type `a`. One way to do this is to represent such a
// stateful computation as a program whose type is `st a`: 
let st a = int -> a & int

let read_and_increment_v0
  : st int
  = fun s0 -> s0, s0 + 1
  
let inc_twice_v0
  : st int
  = fun s0 ->
    let x, s1 = read_and_increment_v0 s0 in
    let _, s2 = read_and_increment_v0 s1 in
    x, s2

let inc_twice_buggy
  : st int
  = fun s0 ->
    let x, s1 = read_and_increment_v0 s0 in
    let _, s2 = read_and_increment_v0 s0 in
    x, s2

let read
  : st int
  = fun s -> s, s
  
let write (s1:int)
  : st unit
  = fun _ -> (), s1
  
let bind #a #b 
         (f: st a)
         (g: a -> st b)
  : st b
  = fun s0 ->
      let x, s1 = f s0 in
      g x s1 
      
let return #a (x:a)
  : st a
  = fun s -> x, s
  
// ## Some stateful programs

let read_and_increment_v1 : st int = 
  bind read (fun x -> 
  bind (write (x + 1)) (fun _ -> 
  return x))
  
// ## Monadic let bindings

let (let!) = bind

let read_and_increment : st int =
  let! x = read in
  write (x + 1) ;!
  return x
  
let inc_twice
  : st int
  = let! x = read_and_increment in
    read_and_increment ;!
    return x

// ## `st` is a monad

let feq #a #b (f g : a -> b) = forall x. f x == g x
let left_identity #a #b (x:a) (g: a -> st b)
  : Lemma ((let! v = return x in g v) `feq` g x)
  = ()
let right_identity #a (f:st a)
  : Lemma ((let! x = f in return x) `feq` f)
  = ()
let associativity #a #b #c (f1:st a) (f2:a -> st b) (f3:b -> st c)
  : Lemma ((let! x = f1 in let! y = f2 x in f3 y) `feq`
           (let! y = (let! x = f1 in f2 x) in f3 y))
  = ()
  
let redundant_read_elim ()
  : Lemma ((read;! read) `feq` read)
  = ()

let redundant_write_elim (x y:int)
  : Lemma ((write x ;! write y) `feq` write y)
  = ()

let read_write_noop ()
  : Lemma ((let! x = read in write x) `feq` return ())
  = ()
  
