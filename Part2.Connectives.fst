module Part2.Connectives

// # Constructive & Classical Connectives

// ## Falsehood doesn't have constructors
// type empty =

// let False = squash empty

// The False proposition has no introduction form, since it has no proofs.

let empty_elim (#a:Type) (x:empty) : a = match x with
let rec false_elim (#a:Type) (x:False) : a = false_elim x

// ## Truth has just a single proof(one constructor)
// type trivial = T
// let True = squash trivial

// ### Introduction

// let _ : trivial = T
// let _ : True = ()

// No Elimination

// ## Conjunction is just a pair of proofs of 

type pair (p q:Type) = | Pair : _1:p -> _2:q -> pair p q

let ( /\ ) (p q:Type) = squash (pair p q)

// ### Introduction

let and_intro #p #q (pf_p:p) (pf_q:q)
  : pair p q
  = Pair pf_p pf_q
  
// ### Elimination

let and_elim_1 #p #q (pf_pq:p & q)
  : p
  = pf_pq._1

let and_elim_2 #p #q (pf_pq:p & q)
  : q
  = pf_pq._2

// ## Disjunction

type sum (p q:Type) =
  | Left : p -> sum p q
  | Right : q -> sum p q
  
let ( \/ ) (p q: Type) = squash (sum p q)

// ### Introduction is a just use of Left or Right constructor
// ### Elimination

let sum_elim #p #q #r (p_or_q: sum p q)
                         (pr: p -> r)
                         (qr: q -> r)
  : r
  = match p_or_q with
    | Left p -> pr p
    | Right q -> qr q

// ### Implication

let ( ==> ) (p q : Type) = squash (p -> q)

// Introduction

// open FStar.Classical
// let implies_intro_1 #p #q (pq: squash p -> squash q)
//   : squash (p ==> q)
//   = introduce p ==> q
//     with pf_p. pq pf_p

// let implies_intro_2 #p #q (pq: unit -> Lemma (requires p) (ensures q))
//   : squash (p ==> q)
//   = introduce p ==> q
//     with pf_p. pq pf_p

// let implies_intro_3 #p #q (pq: unit -> Lemma (requires p) (ensures q))
//   : Lemma (p ==> q)
//   = introduce p ==> q
//     with pf_p. pq pf_p

// let implies_intro_1 (#p #q:Type) (pq: (squash p -> squash q))
//   : squash (p ==> q)
//   = FStar.Classical.Sugar.implies_intro
//            p
//            (fun (_: squash p) -> q)
//            (fun (pf_p: squash p) -> pq pf_p)

// ### Elimination

let arrow_elim #p #q (f:p -> q) (x:p) : q = f x

// ## Negation is just a special case of implication.
// In its constructive form, it corresponds to `p -> empty`.

open FStar.Classical.Sugar

let neg_intro_1 #p (f:squash p -> squash False)
  : squash (~p)
  = FStar.Classical.Sugar.implies_intro
      p
      (fun (_: squash p) -> False)
      (fun (pf_p: squash p) -> f pf_p)

let neg_intro #p (f:squash p -> squash False)
  : squash (~p)
  = introduce p ==> False
    with pf_p. f pf_p

let neg_elim #p #q (f:squash (~p)) (lem:unit -> Lemma p)
  : squash q
  = eliminate p ==> False
    with lem()

// ## Universal Quantification

// let ( forall ) #t (q:t -> Type) = squash (x:t -> q x)

// ### Introduction

let forall_intro_1 (#t:Type)
                   (#q:t -> Type)
                   (f : (x:t -> squash (q x)))
  : squash (forall (x:t). q x)
  = introduce forall (x:t). q x
    with f x

let forall_intro_2 (#t:Type)
                   (#q:t -> Type)
                   (f : (x:t -> Lemma (q x)))
  : squash (forall (x:t). q x)
  = introduce forall (x:t). q x
    with f x

let forall_intro_3 (#t0:Type)
                   (#t1:t0 -> Type)
                   (#q: (x0:t0 -> x1:t1 x0 -> Type))
                   (f : (x0:t0 -> x1:t1 x0 ->  Lemma (q x0 x1)))
  : squash (forall (x0:t0) (x1:t1 x0). q x0 x1)
  = introduce forall (x0:t0) (x1:t1 x0). q x0 x1
    with f x0 x1
    
// ### Elimination

let dep_arrow_elim #t #q (f:(x:t -> q x)) (x:t) : q x = f x

let forall_elim_1 (#t:Type)
                  (#q:t -> Type)
                  (f : squash (forall (x:t). q x))
                  (a:t)
  : squash (q a)
  = ()
  
// let forall_elim_2 (#t0:Type)
//                   (#t1:t0 -> Type)
//                   (#q: (x0:t0 -> x1:t1 x0 -> Type))
//                   (f : squash (forall x0 x1. q x0 x1))
//                   (v0: t0)
//                   (v1: t1 v0)
//   : squash (q v0 v1)
//   = eliminate forall x0 x1. q x0 x1
//     with v0 v1
    
//  FStar.Classical.Sugar.forall_elim
//            #(t1 v0)
//            #(fun x1 -> q v0 x1)
//            v1
//            (FStar.Classical.Sugar.forall_elim
//               #t0
//               #(fun x0 -> forall (x1: t1 x0). q x0 x1)
//               v0
//               ())

// ## Existential Quantification

// type dtuple2 (a:Type) (b: a -> Type) =
//    | Mkdtuple2 : x:a -> y:b x -> dtuple2 a b

// let ( exists ) (#a:Type) (#b:a -> Type) = squash (x:a & b x)

// ### Introduction
let dtuple2_intro (x:int) (y:int { y > x })
  : (a:int & b:int{b > a})
  = (| x, y |)
  
// ### Elimination

let dtuple2_elim (#t:Type) (#p:t -> Type) (#q:Type)
                 (pf: (x:t & p x))
                 (k : (x:t -> p x -> q))
  : q
  = let (| x, pf_p |) = pf in
    k x pf_p