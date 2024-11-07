module Part1.Lemmas

// # Lemmas and proofs by induction

open FStar.Mul
let rec factorial (n:nat)
  : nat
  = if n = 0
    then 1
    else n * factorial (n - 1)

// F* cannot do proofs by induction automatically
// let _ = assert (forall (x:nat). x > 2 ==> factorial x > 2)

// ## Introducing lemmas

// A lemmas is a function in F* that always returns the `():unit` value.
// The type of lemma carries useful information about which facts are provable.

let rec factorial_is_positive (x:nat)
  : u:unit{factorial x > 0}
  = if x = 0 then ()
    else factorial_is_positive (x - 1)
    
// ## Some syntactic shorthands for Lemmas

let rec factorial_is_pos (x:nat)
  : Lemma (requires x >= 0)
          (ensures factorial x > 0)
  = if x = 0 then ()
    else factorial_is_pos (x - 1)
    
// ## A proof by induction, explained in detail

(*
  - It's a proof by induction on `x`.
  - The base case of the induction is when `x=0`.
    - `factorial 0 > 0` can be easily proved by computing `factorial 0` to `1`.
  - In the inductive case
    - the type of the induction hypothesis is: `y:int {y < x} -> Lemma (requires y >= 0) (ensures factorial y > 0)`
    - i.e. if `y` is smaller than `x` and non-negative, it's safe to assume `factorial y > 0`.
    - by making a recursive call on `x-1` F* can conclude that `factorial (x - 1) > 0`
    - to prove that `factorial x > 0`, the solver utilizes the fact that `factoral x = x * factorial (x - 1)`
    - the solver knows that `factorial (x - 1) > 0`, and then, can conclude that the product of two positive numbers must be positive. 
*)

// ## Exercise 1
val factorial_is_greater_than_arg (x:int)
  : Lemma (requires x > 2)
          (ensures factorial x > x)
let rec factorial_is_greater_than_arg x
  = if x = 3 then ()
    else factorial_is_greater_than_arg (x - 1)

// ## Exercise 2

let rec fibonacci (n:nat)
  : nat
  = if n <= 1
    then 1
    else fibonacci (n - 1) + fibonacci (n - 2)

val fibonacci_greater_than_arg' (n:nat{n >= 2})
  : Lemma (fibonacci n >= n)
let rec fibonacci_greater_than_arg' n
  = if n = 2 || n = 3 then ()
    else (
      fibonacci_greater_than_arg' (n - 1);
    fibonacci_greater_than_arg' (n - 2)
    )
    
val fibonacci_greater_than_arg (n:nat{n >= 2})
  : Lemma (fibonacci n >= n)
let rec fibonacci_greater_than_arg n
  = if n = 2 then ()
    else fibonacci_greater_than_arg (n - 1)
    
// Exercise: A lemma about append

let rec app #a (l1 l2: list a)
  : list a
  = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: app tl l2

let rec length #a (l:list a)
  : nat
  = match l with
    | [] -> 0
    | _ :: tl -> 1 + length tl
    
let rec app_length (#a: Type) (l1 l2: list a)
  : Lemma (length (app l1 l2) = length l1 + length l2)
  = match l1 with
  | [] -> ()
  | _ :: tl -> app_length tl l2
  
// ## Intrinsic vs extrinsic proofs

let rec append (#a:Type) (l1 l2:list a)
  : list a
  = match l1 with
    | [] -> l2
    | hd::tl -> hd :: append tl l2

// val reverse (#a:Type) : f:(list a -> list a){forall l. l == f (f l)}
let rec reverse #a (l:list a)
  : list a
  = match l with
    | [] -> []
    | hd :: tl -> append (reverse tl) [hd]
  
// snoc is "cons" backwards --- it adds an element to the end of a list
let snoc l h = append l [h]

let rec snoc_cons #a (l:list a) (h:a)
  : Lemma (reverse (snoc l h) == h :: reverse l)
  = match l with
    | [] -> ()
    | hd :: tl -> snoc_cons tl h

let rec rev_involutive #a (l:list a)
  : Lemma (reverse (reverse l) == l)
  = match l with
    | [] -> ()
    | hd :: tl ->
      // (1) [reverse (reverse tl) == tl]
      rev_involutive tl;
      // (2) [reverse (append (reverse tl) [hd]) == h :: reverse (reverse tl)]
      snoc_cons (reverse tl) hd
      // These two facts are enough for Z3 to prove the lemma:
      //   reverse (reverse (hd :: tl))
      //   =def= reverse (append (reverse tl) [hd])
      //   =(2)= hd :: reverse (reverse tl)
      //   =(1)= hd :: tl
      //   =def= l
      
// Exercises: Reverse is injective

let rec snoc_injective (#a: Type) (l1: list a) (h1: a) (l2: list a) (h2: a)
  : Lemma (requires snoc l1 h1 == snoc l2 h2)
          (ensures l1 == l2 /\ h1 == h2)
  = match l1, l2 with
    | _::t1, _::t2 -> snoc_injective t1 h1 t2 h2
    | _ -> ()

let rec rev_injective (#a:Type) (l1 l2:list a)
  : Lemma (requires reverse l1 == reverse l2)
          (ensures  l1 == l2)
  = match l1, l2 with
    | h1::t1, h2::t2 -> 
      // assert(reverse (h1::t1) = reverse (h2::t2));
      // assert(snoc (reverse t1) h1  = snoc (reverse t2) h2);
      snoc_injective (reverse t1) h1 (reverse t2) h2;
      // assert(reverse t1 = reverse t2 /\ h1 = h2);
      rev_injective t1 t2
      // assert(t1 = t2 /\ h1::t1 = h2::t2)
    | _, _ -> ()
    
let rev_injective_alt (#a:Type) (l1 l2:list a)
  : Lemma (requires reverse l1 == reverse l2)
          (ensures  l1 == l2)
  = rev_involutive l1; rev_involutive l2
  
// Exercise: Optimizing reverse

let rec rev_aux #a (l1 l2:list a)
  : Tot (list a) (decreases l2)
  = match l2 with
    | []     -> l1
    | hd :: tl -> rev_aux (hd :: l1) tl

let rev #a (l:list a) : list a = rev_aux [] l

let rec append_assoc #a (l1 l2 l3: list a)
  : Lemma (append l1 (append l2 l3) == append (append l1 l2) l3)
  = match l1 with
    | [] -> ()
    | hd :: tl -> append_assoc tl l2 l3
    
let rec append_right_unit #a (l1:list a)
  : Lemma (append l1 [] == l1)
  = match l1 with
    | [] -> ()
    | _ :: tl -> append_right_unit tl

let rec rev_is_ok_aux #a (l1 l2:list a)
  : Lemma (ensures (rev_aux l1 l2 == append (reverse l2) l1))
          (decreases l2)
  = match l2 with
    | [] -> ()
    | hd :: tl  -> rev_is_ok_aux (hd :: l1) tl;
                 append_assoc (reverse tl) [hd] l1

let rev_is_ok (#a:_) (l:list a)
  : Lemma (rev l == reverse l)
  = rev_is_ok_aux [] l; append_right_unit (reverse l)

// Exercise: Optimizing Fibonacci

let rec fib (a b n:nat)
  : Tot nat (decreases n)
  = match n with
    | 0 -> a
    | _ -> fib b (a+b) (n-1)

let fib_tail (n:nat) : nat = fib 1 1 n


let rec fib_is_ok_aux (n: nat) (k: nat)
  : Lemma (fib (fibonacci k)
               (fibonacci (k + 1)) n == fibonacci (k + n))
  = if n = 0 then () else fib_is_ok_aux (n - 1) (k + 1)

let fib_tail_is_ok (n:nat)
  : Lemma (fib_tail n == fibonacci n)
  = fib_is_ok_aux n 0
  
// ## Higher-order functions

let rec map #a #b (f: a -> b) (l: list a)
  : list b
  = match l with
    | [] -> []
    | hd::tl -> f hd :: map f tl
    
let _ = map (fun x -> x + 1) [0; 1; 2] // = [1; 2; 3]

// Exercise: Finding a list element

val find (#a:Type) (f: a -> bool) (l:list a)
  : o:option a{ Some? o ==> f (Some?.v o)}

let rec find f l =
  match l with
  | [] -> None
  | hd::tl -> if f hd then Some hd else find f tl

let rec find2 f l =
  match l with
  | [] -> None
  | hd::tl -> if f hd then Some hd else find2 f tl
  
let rec find2_ok #a (f:a -> bool) (l:list a)
  : Lemma (match find2 f l with
           | Some x -> f x
           | _ -> true)
  = match l with
    | [] -> ()
    | _ :: tl -> find2_ok f tl
    
// Exercise: fold_left

let rec fold_left #a #b (f: b -> a -> a) (l: list b) (acc:a)
  : a
  = match l with
    | [] -> acc
    | hd :: tl -> fold_left f tl (f hd acc)
    
val fold_left_Cons_is_rev (#a:Type) (l:list a)
  : Lemma (fold_left Cons l [] == reverse l)
  
let rec fold_left_Cons_is_rev_stronger #a (l1 l2: list a)
  : Lemma (fold_left Cons l1 l2 == append (reverse l1) l2)
  = match l1 with
    | [] -> ()
    | h1 :: t1 ->
      // (1) [append (append (reverse t1) [h1]) l2
      //      == append (reverse t1) (append [h1] l2)]
      append_assoc (reverse t1) [h1] l2;
      // (2) [fold_left Cons t1 (h1 :: l2) = append (reverse t1) (h1 :: l2)]
      fold_left_Cons_is_rev_stronger t1 (h1 :: l2)
      // append (reverse l1) l2
      // =def= append (append (reverse t1) [h1]) l2
      // =(1)= append (reverse t1) (append [h1] l2)
      // =def= append (reverse t1) (h1 :: l2)
      // =(2)= fold_left Cons t1 (h1 :: l2)
      // =def= fold_left Cons l1 l2

let fold_left_Cons_is_rev #a (l:list a)
  : Lemma (fold_left Cons l [] == reverse l)
  = fold_left_Cons_is_rev_stronger l [];
    append_right_unit (reverse l)


