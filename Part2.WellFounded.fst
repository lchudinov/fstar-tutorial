module Part2.WellFounded

// # Well-founded Relations and Termination

// ## Well-founded Relations and Accessibility Predicates

let binrel a = a -> a -> Type
noeq
type acc (#a:Type) (r:binrel a) (x0:a) : Type =
  | AccIntro : access_smaller: (x1:a -> r x1 x0 -> acc r x1) -> acc r x0
  
let well_founded (#a:Type) (r:binrel a) = x:a -> acc r x
let is_well_founded (#a:Type) (r:binrel a) = forall x. squash (acc r x)

// ## Well-founded Recursion

let rec fix_F (#aa:Type)
              (#r:binrel aa)
              (#p:(aa -> Type))
              (f: (x:aa -> (y:aa -> r y x -> p y) -> p x))              
              (x0:aa)
              (accessible_x0:acc r x0)
  : Tot (p x0) (decreases accessible_x0)
  = f x0 (fun y r_yx -> fix_F f y (accessible_x0.access_smaller y r_yx))
  
let fix (#aa:Type) (#r:binrel aa) (rwf:well_founded r)
        (p:aa -> Type) (f:(x:aa -> (y:aa -> r y x -> p y) -> p x))
        (x:aa)
  : p x
  = fix_F f x (rwf x)
  
// ## Some Well-founded Relations

let lt_nat (x y:nat) : Type = x < y == true
let rec wf_lt_nat (x:nat)
  : acc lt_nat x
  = AccIntro (fun y _ -> wf_lt_nat y)

let subrel_wf (#a:Type) (#r #sub_r:binrel a)
              (sub_w:(x:a -> y:a -> sub_r x y -> r x y))
              (r_wf:well_founded r)
  : well_founded sub_r
  = let rec aux (x:a)
                (acc_r:acc r x)
      : Tot (acc sub_r x) (decreases acc_r)
      = AccIntro 
          (fun y sub_r_y_x ->
             aux y (acc_r.access_smaller y (sub_w y x sub_r_y_x)))
    in
    fun x -> aux x (r_wf x)
    
let inverse_image (#a #b:Type) (r_b:binrel b) (f:a -> b) : binrel a =
  fun x y -> r_b (f x) (f y)

let inverse_image_wf (#a #b:Type) (#r_b:binrel b)
                     (f:a -> b)
                     (r_b_wf:well_founded r_b)
  : well_founded (inverse_image r_b f)
  = let rec aux (x:a)
                (acc_r_b:acc r_b (f x))
      : Tot (acc (inverse_image r_b f) x)
            (decreases acc_r_b)
      = AccIntro (fun y p -> aux y (acc_r_b.access_smaller (f y) p)) in
    fun x -> aux x (r_b_wf (f x))
    
// ## Termination Checking with Custom Well-founded Relations

noeq
type lexicographic_order (#a:Type)
                         (#b:a -> Type)
                         (r_a:binrel a)
                         (r_b:(x:a -> binrel (b x)))
  : (x:a & b x) -> (x:a & b x) -> Type =
  | Left_lex:
    x1:a -> x2:a ->
    y1:b x1 -> y2:b x2 ->
    r_a x1 x2 ->
    lexicographic_order r_a r_b (| x1, y1 |) (| x2, y2 |)

  | Right_lex:
    x:a ->
    y1:b x -> y2:b x ->
    r_b x y1 y2 ->
    lexicographic_order r_a r_b (| x, y1 |) (| x, y2 |)
    
    
// not complete