module Part3.Typeclasses.Exercises

module TC = FStar.Tactics.Typeclasses

class printable (a:Type) =
{
  to_string : a -> string
}

instance printable_bool : printable bool =
{
  to_string = Prims.string_of_bool
}

instance printable_int : printable int =
{
  to_string = Prims.string_of_int
}

let printb (x:bool) = to_string x
let printi (x:int) = to_string x

instance printable_list (#a:Type) (x:printable a) : printable (list a) =
{
  to_string = (fun l -> "[" ^ FStar.String.concat "; " (List.Tot.map to_string l) ^ "]")
}

let printis (l:list int) = to_string l
let printbs (l:list bool) = to_string l

let print_any_list_explicit #a ( _ : printable a ) (l:list a) = to_string l
let _ = print_any_list_explicit printable_int [1;2;3]

let print_any_list #a {| _ : printable a |} (l:list a) = to_string l
let _ex1 = print_any_list [[1;2;3]]
let _ex2 = print_any_list #_ #(printable_list printable_int) [[1;2;3]]

let print_any_list_alt #a {| printable a |} (l:list a) = to_string l

//Define instances to make this work

instance printable_string : printable string =
{
  to_string = id
}

instance printable_tuple #a #b {| printable a |} {| printable b |}:  printable (a&b)  =
{
  to_string = (fun x -> "(" ^ (to_string (fst x)) ^ (to_string (snd x)) ^ "]")
}

instance printable_option #a {| printable a |} :  printable (option a)  =
{
  to_string = (fun x -> match x with
                        | Some y -> "( option " ^ (to_string y) ^ ")"
                        | None -> "None"
              )
}

instance printable_either #a #b {| printable a |} {| printable b |}:  printable (either a b)  =
{
  to_string = (fun x -> match x with
                        | Inl y -> "( Left " ^ (to_string y) ^ ")"
                        | Inr y -> "( Right " ^ (to_string y) ^ ")"
              )}


let _ = to_string [Inl (0, 1); Inr (Inl (Some true)); Inr (Inr "hello") ]
