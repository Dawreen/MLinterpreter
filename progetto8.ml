type variable = string ;;

(*espressioni*)
type exp =

  | Int of int
  | Bool of bool
  | Tuple of exp list

  | Plus of exp * exp
  | Minus of exp * exp
  | Times of exp * exp
  | Div of exp * exp
  | LessThan of exp * exp
  | LessThanEq of exp * exp
  | And of exp * exp
  | Or of exp * exp
  | Not of exp
  | IsZero of exp

  | IsEmpty of exp
  | In of exp * exp
  | At of exp * exp
  | Slice of exp * exp * exp

  | Ifthenelse of exp * exp * exp

  | Den of variable
  | Let of variable * exp * exp

  | Fun of variable * exp
  | Apply of exp * exp

  | For of variable * exp * exp

;;

(*definizione del modulo ambiente*)
module type ENV =
  sig
    type 't env
    val emptyenv : 't -> 't env
    val bind : 't env * string * 't -> 't env
    val applyenv : 't env * string -> 't
end;;

module Listenv:ENV =
struct
  type 't env = (string * 't) list
  exception WrongBindlist
  let emptyenv(x) = [("", x)]
  let rec applyenv(x,y) = match x with
    | (i1, e1) :: x1 -> if y = i1 then e1
      else applyenv(x1, y)
    | [] -> failwith("wrong env")
  let bind(r, l, e) = (l, e) :: r
end;;

(*tupi valutati dall'interprete*)
type eval =
  | Eint of int
  | Ebool of bool
  | Etuple of eval list
  | Funval of efun
  | Unbound
and efun = exp * eval Listenv.env;; (*ambiente al momento della dichiarazione*)

(*funzione ausiliariare per implementare At*)
let rec atPos(x, l) = 	match (x, l) with
  | _ , [] -> failwith("not defined")
  | k, l1 -> if k = 0 then List.hd(l1) else
    (if k > 0 then atPos( k-1, List.tl(l1)) else(
      if k = -1 then List.hd(List.rev(List.tl(l1))) else atPos( k+1, List.tl(l1))))
;;
(*funzione ausiliariare per implementare Slice*)
let rec slice (i, f, l2) = match (i, f, l2) with
  | _ , _ , [] -> failwith "not defined"
  | x , y , l -> if x=y then atPos(x, l)::[] else(
    if x<y then atPos(x, l):: slice(x+1, y, l) else
      failwith "oreder integers incorrect"
    )
;;

let rec sem (e, r) = match e with
  | Int(n) -> Eint(n)
  | Bool(b) -> Ebool(b)
  | Tuple(t) -> Etuple( List.map ( fun x -> sem(x, r)) t)
(*operazioni base su interi*)
  | Plus(a, b) -> (match (sem(a, r), sem(b, r)) with
    | Eint(x), Eint(y) -> Eint(x + y)
    | _, _ -> failwith "non integer argument"
  )
  | Minus(a, b) -> (match (sem(a, r), sem(b, r)) with
    | Eint(x), Eint(y) -> Eint(x - y)
    | _, _ -> failwith "non integer argument"
  )
  | Times(a, b) -> (match (sem(a, r), sem(b, r)) with
    | Eint(x), Eint(y) -> Eint(x * y)
    | _, _ -> failwith "non integer argument"
  )
  | Div(a, b) -> (match (sem(a, r), sem(b, r)) with
    | Eint(x), Eint(y) -> Eint(x / y)
    | _, _ -> failwith "non integer argument"
  )
  | LessThan(a, b) -> (match (sem(a, r), sem(b, r)) with
    | Eint(x), Eint(y) -> Ebool(x < y)
    | _, _ -> failwith "non integer argument"
  )
  | LessThanEq(a, b) -> (match (sem(a, r), sem(b, r)) with
    | Eint(x), Eint(y) -> Ebool(x <= y)
    | _, _ -> failwith "non integer argument"
  )
  | IsZero(a) -> (match sem(a, r) with
    | Eint(x) -> Ebool(x = 0)
    | _ -> failwith "non integer argument"
  )
(*operazioni base su boleani*)
  | And(a, b) -> (match (sem(a, r), sem(b, r)) with
    | Ebool(x), Ebool(y) -> Ebool(x && y)
    | _, _ -> failwith "non integer argument"
  )
  | Or(a, b) -> (match (sem(a, r), sem(b, r)) with
    | Ebool(x), Ebool(y) -> Ebool(x || y)
    | _, _ -> failwith "non integer argument"
  )
  | Not(a) -> (match sem(a, r) with
    | Ebool(x) -> Ebool(not x)
    | Eint(x) -> Eint(-x)
    | _  -> failwith "non integer or boolean argument"
  )
(*operazioni su tuple*)
  | IsEmpty(a) -> (match sem(a, r) with
    | Etuple([]) -> Ebool(true)
    | Etuple(_) -> Ebool(false)
    | _ -> failwith "non tuple argument"
  )
  | In(a, t) -> (match (sem(a, r), sem(t, r)) with
    | (x, Etuple(l)) -> Ebool( List.mem x l)
    | _ -> failwith "error type argument"
  )
  | At(a, t) -> (match (sem(a, r), sem(t, r)) with
    | (Eint(x), Etuple(l)) -> atPos(x, l)
    | _ -> failwith "error type argument"
  )
  | Slice(a, b, c) -> ( match (sem(a, r), sem(b, r), sem(c, r)) with
    | (Eint(x), Eint(y), Etuple(t)) -> Etuple(slice(x, y, t))
    | _ -> failwith "type error argument"
  )
  | For(a, t, f) -> (match sem(t, r) with
    | Etuple(t1) -> foreach(a, t1, f, r)
    | _ -> failwith "non tuple argument"
  )

  | Ifthenelse(a, b, c) -> (match sem(a, r) with
    | Ebool(true) -> sem(b, r)
    | Ebool(false) -> sem(c, r)
    | _ -> failwith "non boolean guard"
  )

  | Den(i) -> Listenv.applyenv(r, i)
  | Let(i, e1, e2) -> sem(e2, Listenv.bind (r, i, sem(e1, r)))

(*valutazione funzioni*)
  | Fun(_, _) -> Funval(e, r) (*scoping statico*)
  | Apply(e1, e2) -> (match sem( e1, r) with
    | Funval( Fun(x, a), r1) -> sem( a, Listenv.bind(r1, x, sem(e2, r)))
    | _ -> failwith(" no function in apply")
  )(*in Apply l'ambiente non locale della funzione (r1) è quello esistente al
  momento in cui viene valutata l'astrazione*)

and foreach (x, lst, corpo, r) =
  let rec map l f = match l with
    | [] -> []
    | x::xs -> (let bo = try Some(f x) with _ -> None in
      match bo with
        | None -> map xs f
        | Some(e) -> e :: map xs f
  )
  in
  Etuple(map lst (fun el -> sem(corpo, Listenv.bind(r, x, el))))
;;

(* ============================ TEST ============================ *)

(*dato un eval ne stampa a video il tipo*)
let rec evalToString e = match e with
  | Eint(x) -> string_of_int x
  | Ebool(x) -> string_of_bool x
  | Etuple(l) -> (List.fold_left (fun a b -> a ^ " " ^ b) "(" (List.map evalToString l)) ^ " )"
  | Funval(_, _) -> "<fun>"
  | Unbound -> "<unbound>"
;;

(* verifica test *)
(* data  una lista formata da espressioni da valutare ed il loro risultato valutato
ne restituisce una lista formata dal risultato attule e se tale risultato coincide con
quello atteso*)

let test_list = [
  ( Int(42), Eint(42));
  ( Bool(true), Ebool(true));
  ( Tuple([Int(4); Bool(true); Bool(false); Int(2)]), Etuple([Eint(4); Ebool(true); Ebool(false); Eint(2)]));
  ( Plus(Int(1), Int(1)), Eint(2) );
  ( Minus(Int(10), Int(2)), Eint(8));
  ( Times(Int(6), Int(7)), Eint(42));
  ( Div(Int(100), Int(25)), Eint(4));
  ( LessThan(Int(3), Int(42)), Ebool(true));
  ( LessThanEq(Int(42), Int(3)), Ebool(false));
  ( IsZero( Int(7)), Ebool(false));
  ( And(Bool(true), Bool(true)), Ebool(true));
  ( Or(Bool(false), Bool(false)), Ebool(false));
  ( Not(Int(70)), Eint(-70));
  ( Not(Bool(true)), Ebool(false));
  ( IsEmpty(Tuple([])), Ebool(true));
  ( In(Bool(true), Tuple([Int(42); Bool(false); Int(3)]) ), Ebool(false));
  ( At(Int(1), Tuple([Bool(false); Int(42); Tuple([])])), Eint(42));
  ( Slice(Int(1), Int(3), Tuple([Int(1); Int(2); Bool(true); Plus(Int(4), Int(5)); Int(3)])), Etuple([Eint(2); Ebool(true); Eint(9)]));
  ( For("x", Tuple([Int(1); Int(2); Int(3)]), Plus(Den("x"), Int(2))), Etuple([Eint(3); Eint(4); Eint(5)]));
  ( For("x", Tuple([Int(1); Int(2); Bool(true); Plus(Int(4), Int(5)); Int(3)]), Plus(Den("x"), Int(2))), Etuple([Eint(3); Eint(4); Eint(11); Eint(5)]));
  ( IsZero(Minus(Int(4), Times(Int(2), Int(2)))), Ebool(true));
  ( Ifthenelse( Bool(false), Bool(false), Bool(true)), Ebool(true));
  ( Ifthenelse( Bool(true), Bool(false), Bool(true)), Ebool(false));
  ( Let("x", Plus(Int(1), Int(4)),
      Let("y", Times(Minus(Den "x", Int(1)), Plus(Den("x"), Int(1))),
        Let("z", Div(Plus(Den("y"), Int(1)), Den("x")), Den ("z"))
        )
    )
  , Eint(5))
];;

List.iter (fun (test, ris) ->
  let r = sem(test, Listenv.emptyenv(Unbound)) in
  let success = r = ris in
  print_endline ((evalToString r) ^ " " ^ (string_of_bool success))
) test_list


(*a cura di Dan Dorin Izvoreanu*)
