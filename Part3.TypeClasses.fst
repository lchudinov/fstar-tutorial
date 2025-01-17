module Part3.TypeClasses

// # Printable
class printable (a: Type) = 
{
  to_string: a -> string
}

// To define instances of a typeclass, one uses the `instance` keyword, as shown below.

instance printable_bool : printable bool = {
  to_string = Prims.string_of_bool
}

instance printable_int : printable int = {
  to_string = Prims.string_of_int
}

let printb (x:bool) = to_string x
let printi (x:int) = to_string x

// Instances need not only for base types. For example, all lists are printable so long as their
// elements are, and this is captured by what follows.

// Instances (of some type or behavior in a system) are not restricted to base types.
// For example, lists are considered printable as long as their elements are printable.
// This principle or rule will be explained in detail in the following text.

instance printable_list (#a:Type) (x:printable a) : printable (list a) =
{
  to_string = (fun l -> "[" ^ FStar.String.concat "; " (List.Tot.map to_string l) ^ "]")
}

let printis (l:list int) = to_string l
let printbs (l:list bool) = to_string l

let print_any_list_explicit #a (_: printable a) (l:list a) = to_string l
let _ = print_any_list_explicit printable_int [1;2;3]

let print_any_list #a {| _ : printable a |} (l:list a) = to_string l
let _ex1 = print_any_list [[1;2;3]]
let _ex2 = print_any_list #_ #(printable_list printable_int) [[1;2;3]]

let print_any_list_alt #a {| printable a |} (l:list a) = to_string l

// ## Bounded Unsigned Integers

class bounded_unsigned_int (a:Type) = {
  bound: a;
  as_nat: a -> nat;
  from_nat: (x: nat { x <= as_nat bound } -> a);
  [@@@FStar.Tactics.Typeclasses.no_method]
  properties : squash (
    (forall (x:a). as_nat x <= as_nat bound) /\
    (forall (x:a). from_nat (as_nat x) == x) /\
    (forall (x:nat{ x <= as_nat bound}). as_nat (from_nat x) == x)
  )
}

let fits #a {| bounded_unsigned_int a |}
            (op: int -> int -> int)
            (x y:a)
  : prop
  = 0 <= op (as_nat x) (as_nat y) /\
    op (as_nat x) (as_nat y) <= as_nat #a bound

let related_ops #a {| bounded_unsigned_int a |}
                (iop: int -> int -> int)
                (bop: (x:a -> y:a { fits iop x y } -> a))
  = forall (x y:a).  fits iop x y ==> as_nat (bop x y) = as_nat x `iop` as_nat y
  
// ## Typeclass Inheritance

module TC = FStar.Tactics.Typeclasses

class bounded_unsigned_int_ops (a:Type) = {
   [@@@TC.no_method]
   base       : bounded_unsigned_int a;
   add        : (x:a -> y:a { fits ( + ) x y } -> a);
   sub        : (x:a -> y:a { fits op_Subtraction x y } -> a);
   lt         : (a -> a -> bool);
   [@@@TC.no_method]
   properties : squash (
     related_ops ( + ) add /\
     related_ops op_Subtraction sub /\      
     (forall (x y:a). lt x y <==> as_nat x < as_nat y) /\ // lt is related to <
     (forall (x:a). fits op_Subtraction bound x) //subtracting from the maximum element never triggers underflow
   )
}

instance ops_base #a {| d : bounded_unsigned_int_ops a |} 
  : bounded_unsigned_int a
  = d.base
  
// # Infix Operators

let ( +^ ) #a {| bounded_unsigned_int_ops a |}
           (x : a)
           (y : a { fits ( + ) x y })
  : a
  = add x y

let ( -^ ) #a {| bounded_unsigned_int_ops a |}
           (x : a)
           (y : a { fits op_Subtraction x y })
  : a
  = sub x y

let ( <^ ) #a {| bounded_unsigned_int_ops a |}
           (x : a)
           (y : a)
  : bool
  = lt x y
  
// # Derived Instances

class eq (a:Type) = {
  eq_op: a -> a -> bool;

  [@@@TC.no_method]
  properties : squash (
    forall x y. eq_op x y <==> x == y
  )
}

let ( =?= ) #a {| eq a |} (x y: a) = eq_op x y

instance bounded_unsigned_int_ops_eq #a {| bounded_unsigned_int_ops a |}
  : eq a
  = {
      eq_op = (fun x y -> not (x <^ y) && not (y <^ x));
      properties = ()
    }

let ( <=^ ) #a {| bounded_unsigned_int_ops a |} (x y : a)
  : bool
  = x <^ y || x =?= y

// # Ground Instances

module U32 = FStar.UInt32
module U64 = FStar.UInt64
instance u32_instance_base : bounded_unsigned_int U32.t =
  let open U32 in
  {
    bound    = 0xfffffffful;
    as_nat   = v;
    from_nat = uint_to_t;
    properties = ()
}

instance u32_instance_ops : bounded_unsigned_int_ops U32.t =
  let open U32 in
  {
    base = u32_instance_base;
    add  = (fun x y -> add x y);
    sub  = (fun x y -> sub x y);
    lt   = (fun x y -> lt x y);
    properties = ()
  }


instance u64_instance_base : bounded_unsigned_int U64.t =
  let open U64 in
  {
    bound    = 0xffffffffffffffffuL;
    as_nat   = v;
    from_nat = uint_to_t;
    properties = ()
}

instance u64_instance_ops : bounded_unsigned_int_ops U64.t =
  let open U64 in
  {
    base = u64_instance_base;
    add  = (fun x y -> add x y);
    sub  = (fun x y -> sub x y);
    lt   = (fun x y -> lt x y);
    properties = ()
  }
  
let test32 (x:U32.t)
           (y:U32.t)
  = if x <=^ 0xffffffful &&
       y <=^ 0xffffffful
    then Some (x +^ y)
    else None

let test64 (x y:U64.t)
  = if x <=^ 0xfffffffuL &&
       y <=^ 0xfffffffuL
    then Some (x +^ y)
    else None
    
module L = FStar.List.Tot
let sum #a {| bounded_unsigned_int_ops a |}
        (l:list a) (acc:a)
  : option a 
  = L.fold_right
     (fun (x:a) (acc:option a) ->
       match acc with
       | None -> None
       | Some y ->
         if x <=^ bound -^ y
         then Some (x +^ y)
         else None)
     l
     (Some acc)

let testsum32 : U32.t = Some?.v (sum [0x01ul; 0x02ul; 0x03ul] 0x00ul)
let testsum64 : U64.t = Some?.v (sum [0x01uL; 0x02uL; 0x03uL] 0x00uL)

let testsum32' : U32.t =
  let x =
    sum #U32.t
        [0x01ul; 0x02ul; 0x03ul;
         0x01ul; 0x02ul; 0x03ul;
         0x01ul; 0x02ul; 0x03ul]
        0x00ul
  in
  assert_norm (Some? x /\ as_nat (Some?.v x) == 18);
  Some?.v x
  
// # Dealing with Diamonds

// class subtractable_bounded_unsigned_int (a:Type) = {
//    [@@@TC.no_method]
//    base   : bounded_unsigned_int a;
//    sub    : (x:a -> y:a { fits op_Subtraction x y } -> a);

//    [@@@TC.no_method]
//    properties : squash (
//      related_ops op_Subtraction sub /\
//      (forall (x:a). fits op_Subtraction bound x)
//    )
// }

// instance subtractable_base {| d : subtractable_bounded_unsigned_int 'a |} 
//   : bounded_unsigned_int 'a 
//   = d.base
  
// class comparable_bounded_unsigned_int (a:Type) = {
//    [@@@TC.no_method]
//    base   : bounded_unsigned_int a;
//    comp   : a -> a -> bool;

//    [@@@TC.no_method]
//    properties : squash (
//      (forall (x y:a).{:pattern comp x y} comp x y <==> as_nat x < as_nat y)
//    )
// }

// instance comparable_base {| d : comparable_bounded_unsigned_int 'a |} 
//   : bounded_unsigned_int 'a 
//   = d.base
  
// [@@expect_failure [19]]
// let try_sub #a {| s: subtractable_bounded_unsigned_int a|}
//                {| c: comparable_bounded_unsigned_int a |}
//             (acc:a)
//   = bound `sub` acc

// # Overloading Monadic Syntax

class monad (m:Type -> Type) =
{
  return : (#a:Type -> a -> m a);
  ( let! ) : (#a: Type -> #b: Type -> (f: m a) -> (g:(a -> m b)) -> m b);
}

let st (s:Type) (a:Type) = s -> a & s

instance st_monad s : monad (st s) =
{
  return = (fun #a (x:a) -> (fun s -> x, s));
  ( let! ) = (fun #a #b (f: st s a) (g: a -> st s b) (s0:s) ->
            let x, s1 = f s0 in
            g x s1);
}

let get #s
  : st s s
  = fun s -> s, s

let put #s (x:s)
  : st s unit
  = fun _ -> (), x

let get_inc =
  let! x = get in
  return (x + 1)
  
let get_put #s =
  let! x = get #s in
  put x

let noop #s : st s unit = return ()

let get_put_identity (s:Type)
  : Lemma (get_put #s `FStar.FunctionalExtensionality.feq` noop #s)
  = ()
  
instance opt_monad : monad option =
{
   return = (fun #a (x:a) -> Some x);
   ( let! ) = (fun #a #b (x:option a) (y: a -> option b) ->
             match x with
             | None -> None
             | Some a -> y a)
}

let raise #a : option a = None

let div (n m:int) =
  if m = 0 then raise
  else return (n / m)

let test_opt_monad (i j k:nat) =
  let! x = div i j in
  let! y = div i k in
  return (x + y)
  
class monoid (a:Type) =
{
   op   : a -> a -> a;
   one  : a;
   properties: squash (
     (forall (x:a). op one x == x /\ op x one == x) /\
     (forall (x y z:a). op x (op y z) == op (op x y) z)
   );
}

instance monoid_nat_plus : monoid nat =
{
  op = (fun (x y:nat) -> x + y);
  one = 0;
  properties = ()
}

class graded_monad (#index:Type) {| monoid index |}
                   (m : index -> Type -> Type) = 
{
  return' : #a:Type -> x:a -> m one a;
  
   ( let+ )   : #a:Type -> #b:Type -> #ia:index -> #ib:index ->
           m ia a -> 
           (a -> m ib b) ->
           m (op ia ib) b

}