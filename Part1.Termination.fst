module Part1.Termination

// # Proofs of termination

// If F* didn't check termination, one could write non-terminating functions like this:
// let rec loop (x:unit) : False = loop x

// ## A well-founded partial order on terms

// To prove a function terminating in F* one provides a measure: a pure expression depending on function arguments.
// F* checks that this measure strictly decreases on each recursive call.
// The measure for the arguments of the call is compared to the measure for the previous call according to a well-founded partial order on F* terms.
// We write v1 << v2 when v1 precedes v2 in this order.

// Well-founded means no infinite descending chains in the relation. For example, < is a well-founded partial order on natural numbers.

// Why length terminates

let rec length #a (l:list a)
  : Tot nat (decreases l)
  = match l with
    | [] -> 0
    | _ :: tl -> length tl

// ## Lexicographic orderings

// F* accepts that the following lexicographic ordering:  
// `v1 << u1 ‌‌\/ (v1 == u1 /\ (v2 << u2 ‌‌\/ (v2 == u2 /\ ( ... vn << un))))`

// The shorthand notation is: `%[v1; v2; ...; vn] << %[u1; u2; ...; un]`

let rec ackermann (m n: nat)
  : Tot nat (decreases %[m;n])
  = if m = 0 then n + 1
  else if n = 0 then ackermann (m - 1) 1
  else ackermann (m - 1) (ackermann m (n - 1))
  
// ## Default measures

// F* uses a simple heuristic to choose the decreases clause, if the user didn't provide one.

let rec length' #a (l:list a)
  : nat
  = match l with
    | [] -> 0
    | _ :: tl -> length' tl
    
let rec ackermann' (m n:nat)
  : nat
  = if m=0 then n + 1
    else if n = 0 then ackermann' (m - 1) 1
    else ackermann' (m - 1) (ackermann' m (n - 1))

// The default decreases clause for a total, recursive function is the lexicographic ordering of all the non-function-typed arguments,
// taken in order from left to right.

// The default decreases clause for ackermann is exactly decreases %[m; n]
// The default for length is just decreases %[a; l] (which is equivalent to decreases l). So, we needn't write it.

// if we were to flip the order of arguments to ackermann,
// then the default choice of the measure would not be correct - so, we'll have to write it explicitly:
let rec ackermann_flip (n m:nat)
  : Tot nat (decreases %[m;n])
  = if m = 0 then n + 1
    else if n = 0 then ackermann_flip 1 (m - 1)
    else ackermann_flip (ackermann_flip (n - 1) m) (m - 1)

// ## Mutual recursion

type tree =
  | Terminal : tree
  | Internal : node -> tree

and node = {
  left: tree;
  data: int;
  right: tree;
}

// F* is able to prove that these functions terminate, just by using the default measure as usual.

let rec incr_tree (x: tree)
  : tree
  = match x with
  | Terminal -> Terminal
  | Internal node -> Internal (incr_node node)

and incr_node (n: node)
  : node
  = {
      left = incr_tree n.left;
      data = n.data + 1;
      right = incr_tree n.right;
    }
    
// 

let rec foo (l:list int)
  : Tot int (decreases %[l;0])
  = match l with
    | [] -> 0
    | x :: xs -> bar xs
and bar (l:list int)
  : Tot int (decreases %[l;1])
  = foo l

// # Exercises

// ## Fibonacci in linear time

let rec fibonacci (n:nat)
  : nat
  = if n <= 1
    then 1
    else fibonacci (n - 1) + fibonacci (n - 2)

// Tail-recursive variant
let rec fib (a b n: nat)
  : Tot nat (decreases n)
  =
   match n with
   | 0 -> a
   | _ -> fib b (a+b) (n-1)

let fibonacci' n = fib 1 1 n

// ## Tail-recursive reversal

// let rec rev #a (l:list a)
//   : list a
//   = match l with
//     | [] -> []
//     | hd::tl -> append (rev tl) hd
    
let rec rev_aux (#a: Type) (l1 l2: list a)
  : Tot (list a) (decreases l2)
  =
  match l2 with
  | []     -> l1
  | hd :: tl -> rev_aux (hd :: l1) tl

let rev l = rev_aux [] l
