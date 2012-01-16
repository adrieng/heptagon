(** Define qualified names "Module.name" (longname)
    [shortname] longname -> name
    [fullname] longname -> Module.name *)

type name = string
type module_name = name

type modul =
  | Pervasives
  | LocalModule of modul (** the static parameters of module_name *)
  | Module of module_name
  | QualModule of qualname

and qualname = { qual: modul; name: name }

type type_name = qualname
type fun_name = qualname
type field_name = qualname
type constructor_name = qualname
type constant_name = qualname


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

module NamesSet = Set.Make (struct type t = string let compare = compare end)
module QualSet = Set.Make (struct type t = qualname let compare = compare end)
module ModulSet = Set.Make (struct type t = modul let compare = compare end)

let rec modul_to_string m = match m with
  | Pervasives -> "Pervasives"
  | LocalModule m -> "LOCAL_param_of_" ^ (modul_to_string m)
  | Module n -> n
  | QualModule {qual = q; name = n} -> (modul_to_string q) ^"."^ n

let shortname { name = n; } = n

let modul { qual = m; } = m

let pervasives_qn name = { qual = Pervasives; name = name }

let dummy_qualname = pervasives_qn "dummy"

let fullname {qual = q; name = n} = modul_to_string q ^ "." ^ n


(** Are infix
    [or], [quo], [mod], [land], [lor], [lxor], [lsl], [lsr], [asr]
    and every names not beginning with 'a' .. 'z' | 'A' .. 'Z' | '_' | '`'*)
let is_infix q = match q with
  | { qual = Pervasives; name = s } ->
      let module StrSet = Set.Make(String) in
      let infix_set =
        List.fold_right StrSet.add
          ["or"; "quo"; "mod"; "land"; "lor"; "lxor"; "lsl"; "lsr"; "asr"]
          StrSet.empty in
      if StrSet.mem s infix_set then true
      else begin
        try match String.get s 0 with
              | 'a' .. 'z' | 'A' .. 'Z' | '_' | '`' | '~' -> false
              | _ -> true
        with Invalid_argument _ -> (* empty string *) false
      end
  | _ -> false


let is_op q = match q with
  | { qual = Pervasives; name = s } -> true
  | _ -> false


open Format

(* printers should prevent printing infix names *)
let print_name ff n =
(*  let n = if is_infix n
  then "(" ^ (n ^ ")") (* printers should have a special case to print '*' infix *)
  else n
  in*) fprintf ff "%s" n

(** Use a printer to generate a string compatible with a name *)
let print_pp_to_name p x =
  Misc.sanitize_string (Misc.print_pp_to_string p x)
