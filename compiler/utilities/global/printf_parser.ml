open Signature

exception Bad_format

type token = Modifier of string | Literal of string
type format = token list

let tail s start =
  String.sub s start (String.length s - start)

(** Return a list of expected types from a format string *)
let rec format_of_string s =
  try
    let i = String.index s '%' in
    let l = format_of_string (tail s (i+2)) in
    if i = 0 then
      let modifier = String.sub s 0 1 in
      (Modifier modifier)::l
    else
      let lit = String.sub s 0 i in
      let modifier = String.sub s (i+1) 1 in
      (Literal lit)::(Modifier modifier)::l
  with
    | Invalid_argument _ -> raise Bad_format (* String.get failed*)
    | Not_found -> [Literal s]

let types_of_format_string s =
  let ty_of_format f acc = match f with
    | Modifier "b" -> Initial.tbool::acc
    | Modifier "d" -> Initial.tint::acc
    | Modifier "f" -> Initial.tfloat::acc
    | _ -> acc
  in
  let sl = format_of_string s in
  List.fold_right ty_of_format sl []

let tr_format f s =
  let aux tok acc = match tok with
    | Literal s -> s^acc
    | Modifier m -> "%"^(f m)^acc
  in
  let sl = format_of_string s in
  List.fold_right aux sl ""
