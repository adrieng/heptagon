(** Define qualified names "Module.name" (longname)
    [shortname] longname -> name
    [fullname] longname -> Module.name *)

type name = string

type longname =
  | Name of name
  | Modname of qualident

and qualident = { qual: string; id: string }

type type_name = longname

type fun_name = longname

type field_name = longname

type constructor_name = longname

type constant_name = longname


module NamesM = struct
  type t = name
  let compare = compare
end

module NamesEnv =
struct
  include (Map.Make(NamesM))

  let append env0 env =
    fold (fun key v env -> add key v env) env0 env
end

module LongNameEnv = Map.Make (struct
                                 type t = longname
                                 let compare = compare
                               end)

module S = Set.Make (struct type t = string let compare = compare end)


let shortname = function
  | Name s -> s
  | Modname { id = id; } -> id

let fullname = function
  | Name s -> s
  | Modname { qual = qual; id = id; } -> qual ^ "." ^ id

let mk_longname s =
  try
    let ind = String.index s '.' in
    if ind = 0 || ind = String.length s - 1
    then invalid_arg "mk_longname: ill-formed identifier";
    let id = String.sub s (ind + 1) (String.length s - ind - 1) in
    Modname { qual = String.sub s 0 ind; id = id; }
  with Not_found -> Name s

(** Are infix
    [or], [quo], [mod], [land], [lor], [lxor], [lsl], [lsr], [asr]
    and every names not beginning with 'a' .. 'z' | 'A' .. 'Z' | '_' | '`'*)
let is_infix s =
  let module StrSet = Set.Make(String) in
  let infix_set =
    List.fold_right StrSet.add
      ["or"; "quo"; "mod"; "land"; "lor"; "lxor"; "lsl"; "lsr"; "asr"]
      StrSet.empty in
  if StrSet.mem s infix_set then true
  else (match String.get s 0 with
          | 'a' .. 'z' | 'A' .. 'Z' | '_' | '`' -> false
          | _ -> true)

let print_name ff n =
  let n = if is_infix n
  then "( " ^ (n ^ " )") (* do not remove the space around n, since for example
                            "(*" would create bugs *)
  else n
  in Format.fprintf ff "%s" n

let print_longname ff n =
  match n with
    | Name m -> print_name ff m
    | Modname { qual = "Pervasives"; id = m } -> print_name ff m
    | Modname { qual = m1; id = m2 } ->
        Format.fprintf ff "%s." m1;
        print_name ff m2


