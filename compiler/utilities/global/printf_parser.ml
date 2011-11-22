open Types

exception Bad_format

let tail s start =
  String.sub s start (String.length s - start)

(** Return a list of expected types from a format string *)
let rec extract_formatters s =
  try
    let i = String.index s '%' in
    let ty = match s.[i+1] with
      | 'b' -> Initial.tbool
      | 'd' -> Initial.tint
      | 'f' -> Initial.tfloat
      | _ -> raise Bad_format
    in
    ty::(extract_formatters (tail s (i+1)))
  with
    | Invalid_argument _ -> raise Bad_format (* String.get failed*)
    | Not_found -> []
