(** Define qualified names "Module.name" (longname)
    [shortname] longname -> name
    [fullname] longname -> Module.name *)

type name = string

and qualname = { qual: string; name: string }

type type_name = qualname
type fun_name = qualname
type field_name = qualname
type constructor_name = qualname
type constant_name = qualname
type module_name = name


let local_qualname = "$$%local_current_illegal_module_name%$$"
let local_qn name = { qual = local_qualname; name = name }

module NamesEnv = struct
  include (Map.Make(struct type t = name let compare = compare end))
  let append env0 env = fold (fun key v env -> add key v env) env0 env
end

module QualEnv = struct
  include (Map.Make(struct type t = qualname let compare = compare end))

  (** [append env' env] appends env' to env *)
  let append env' env = fold (fun key v env -> add key v env) env' env
end

module S = Set.Make (struct type t = string let compare = compare end)


let shortname { name = n; } = n

let fullname { qual = qual; name = n; } = qual ^ "." ^ n

let qualname_of_string s =
  try
    let ind = String.index s '.' in
    if ind = 0 || ind = String.length s - 1
    then invalid_arg "mk_longname: ill-formed identifier";
    let n = String.sub s (ind + 1) (String.length s - ind - 1) in
    { qual = String.sub s 0 ind; name = n; }
  with Not_found -> { qual = ""; name = s }

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

open Format

let print_name ff n =
  let n = if is_infix n
  then "( " ^ (n ^ " )") (* do not remove the space around n, since for example
                            "(*" would create bugs *)
  else n
  in fprintf ff "%s" n

let opname qn = match qn with
  | { qual = "Pervasives"; name = m; } -> m
  | { qual = qual; name = n; } -> qual ^ "." ^ n
