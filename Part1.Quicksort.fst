module Part1.Quicksort

let rec sorted (l: list int)
  : bool
  = match l with
    | [] -> true
    | [x] -> true
    | x :: y :: xs -> x <= y && sorted (y :: xs)
    
let rec mem (#a:eqtype) (i:a) (l:list a)
  : bool
  = match l with
    | [] -> false
    | hd :: tl -> hd = i || mem i tl 
    
// forall l. sorted (sort l) /\ (forall i. mem i l <==> mem i (sort l))

// Some auxiliary definitions to make this a standalone example

let rec length #a (l:list a)
  : nat
  = match l with
    | [] -> 0
    | _ :: tl -> 1 + length tl

let rec append #a (l1 l2:list a)
  : list a
  = match l1 with
    | [] -> l2
    | hd :: tl -> hd :: append tl l2
    
// ## Implementing `partition` 

let rec partition (#a:Type) (f:a -> bool) (l: list a)
  : x:(list a & list a) {length (fst x) + length (snd x) = length l}
  = match l with
  | [] -> [], []
  | hd::tl ->
    let l1, l2 = partition f tl in
    if f hd
    then hd::l1, l2
    else l1, hd::l2
    
// ## Implementing `sort`

let rec sort (l:list int)
  : Tot (list int) (decreases (length l))
  = match l with
    | [] -> []
    | pivot :: tl ->
      let hi, lo = partition ((<=) pivot) tl in
      append (sort lo) (pivot :: sort hi) 

// The notation `(<=) pivot` is equivalent to `fun x -> pivot <= x`
// We prove that `sort` terminates with the measure of `length l`.
// At each recursive call, we're claiming that the length of the input is strictly decreasing.
// It's true because the recursive calls `sort lo` and `sort hi` are partitions
// of the `tl` list, which is strictly shorter than `l`, since we've removed the `pivot` element.

// ## Proving `sort` correct

let rec partition_mem (#a:eqtype) (f:(a -> bool)) (l:list a)
  : Lemma (let l1, l2 = partition f l in
           (forall x. mem x l1 ==> f x) /\
           (forall x. mem x l2 ==> not (f x)) /\
           (forall x. mem x l = (mem x l1 || mem x l2)))
  = match l with
  | [] -> ()
  | hd :: tl -> partition_mem f tl
  
let rec sorted_concat (l1:list int{sorted l1})
                      (l2:list int{sorted l2})
                      (pivot:int)
  : Lemma (requires (forall y. mem y l1 ==> not (pivot <= y)) /\
                    (forall y. mem y l2 ==> pivot <= y))
          (ensures sorted (append l1 (pivot :: l2)))
  = match l1 with
    | [] -> ()
    | hd :: tl -> sorted_concat tl l2 pivot
    
let rec append_mem (#t:eqtype)
                   (l1 l2:list t)
  : Lemma (ensures (forall a. mem a (append l1 l2) = (mem a l1 || mem a l2)))
  = match l1 with
    | [] -> ()
    | hd::tl -> append_mem tl l2

let rec sort_correct (l:list int)
  : Lemma (ensures (
           let m = sort l in
           sorted m /\
           (forall i. mem i l = mem i m)))
          (decreases (length l))
  = match l with
  | [] -> ()
  | pivot :: tl ->
    let hi, lo = partition ((<=) pivot) tl in
    sort_correct hi;
    sort_correct lo;
    partition_mem ((<=) pivot) tl;
    sorted_concat (sort lo) (sort hi) pivot;
    append_mem (sort lo) (pivot :: sort hi)

let sort_ok (l:list int) =
    let m = sort l in
    sorted m /\
    (forall i. mem i l = mem i m)

let rec sort_annotaned_correct (l:list int)
  : Lemma (ensures sort_ok l)
          (decreases (length l))
  = match l with
    | [] -> ()
    | pivot :: tl ->
      let hi, lo = partition ((<=) pivot) tl in
      assert (length lo + length hi == length tl);
      sort_annotaned_correct hi;
      assert (sort_ok hi);
      sort_annotaned_correct lo;
      assert (sort_ok lo);
      partition_mem ((<=) pivot) tl;
      assert (forall i. mem i tl = mem i hi || mem i lo);
      assert (forall i. mem i hi ==> pivot <= i);
      assert (forall i. mem i lo ==> i < pivot);
      assert (sort l == (append (sort lo) (pivot :: sort hi)));
      sorted_concat (sort lo) (sort hi) pivot;
      assert (sorted (sort l));
      append_mem (sort lo) (pivot :: sort hi);
      assert (forall i. mem i l = mem i (sort l))