(** Define qualified names "Module.name" (longname)
    [shortname] longname -> name
    [fullname] longname -> Module.name *)

type name = string
type module_name = name

type modul =
  | Pervasives
  | LocalModule
  | Module of module_name
  | QualModule of qualname

and qualname = { qual: modul; name: name }

type type_name = qualname
type fun_name = qualname
type field_name = qualname
type constructor_name = qualname
type constant_name = qualname


let pervasives_qn name = { qual = Pervasives; name = name }

let local_qn name = { qual = LocalModule; name = name }


module NamesEnv = struct
  include (Map.Make(struct type t = name let compare = compare end))
  let append env0 env = fold (fun key v env -> add key v env) env0 env
end

module ModulEnv = struct
  include (Map.Make(struct type t = modul let compare = compare end))
  let append env0 env = fold (fun key v env -> add key v env) env0 env
end

module QualEnv = struct
  include (Map.Make(struct type t = qualname let compare = compare end))

  (** [append env' env] appends env' to env *)
  let append env' env = fold (fun key v env -> add key v env) env' env
end

module QualSet = Set.Make (struct type t = qualname let compare = compare end)
module ModulSet = Set.Make (struct type t = modul let compare = compare end)
module S = Set.Make (struct type t = string let compare = compare end)


let shortname { name = n; } = n

let modul { qual = m; } = m

let rec modul_to_string m = match m with
  | Pervasives -> "Pervasives"
  | LocalModule -> "\#$%@#_LOCAL_MODULE"
  | Module n -> n
  | QualModule {qual = q; name = n} -> (modul_to_string q) ^"."^ n

let fullname {qual = q; name = n} = modul_to_string q ^ "." ^ n

let rec modul_of_string_list = function
  | [] -> LocalModule
  | ["Pervasives"] -> Pervasives
  | [q] -> Module q
  | q::q_l -> QualModule {qual = modul_of_string_list q_l; name = q}

let qualname_of_string s =
  let q_l_n = Misc.split_string s "." in
  match List.rev q_l_n with
    | [] -> Misc.internal_error "Names" 0
    | n::q_l -> { qual = modul_of_string_list q_l; name = n }

let modul_of_string s =
  let q_l = Misc.split_string s "." in
  modul_of_string_list (List.rev q_l)

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
          | 'a' .. 'z' | 'A' .. 'Z' | '_' | '`' | '~' -> false
          | _ -> true)

open Format

let print_name ff n =
  let n = if is_infix n
  then "( " ^ (n ^ " )") (* do not remove the space around n, since for example
                            "(*" would create bugs *)
  else n
  in fprintf ff "%s" n

(** Use a printer to generate a string compatible with a name *)
let print_pp_to_name p x =
  Misc.sanitize_string (Misc.print_pp_to_string p x)
