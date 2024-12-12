module Part2.PHOAS

// # Higher-order Abstract Syntax

type typ =
  | Bool
  | Int
  | Arrow : typ -> typ -> typ

let rec denote_typ (t:typ)
  : Type
  = match t with
    | Bool -> bool
    | Int -> int
    | Arrow t1 t2 -> (denote_typ t1 -> denote_typ t2)
    
noeq
type term : typ -> Type =
  | Var : #t:typ -> denote_typ t -> term t
  | TT  : term Bool
  | FF  : term Bool
  | I   : int -> term Int
  | App : #t1:typ -> #t2:typ ->
          term (Arrow t1 t2) ->
          term t1 ->
          term t2
  | Lam : #t1:typ -> #t2:typ ->
          (denote_typ t1 -> term t2) ->
          term (Arrow t1 t2)
          
// ## Denotation of terms

let rec denote_term (#t:typ) (e:term t)
  : Tot (denote_typ t)
        (decreases e)
  = match e with
    | Var x -> x
    | TT -> true
    | FF -> false
    | I i -> i
    | App f a -> (denote_term f) (denote_term a)
    | Lam f -> fun x -> denote_term (f x)
    
