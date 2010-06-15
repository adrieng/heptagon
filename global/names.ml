(* long identifiers *)

type name = string

type longname =
    | Name of name
    | Modname of qualident

and qualident = { qual: string; id: string }

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
    let id = String.sub s (ind + 1) (String.length s - ind - 1) in
    Modname { qual = String.sub s 0 ind; id = id; }
  with Not_found -> Name s

let fprint_t ff id = Format.fprintf ff "%s" (fullname id)
