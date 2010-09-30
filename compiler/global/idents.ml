(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* naming and local environment *)


type ident = {
  num : int;        (* a unique index *)
  source : string;  (* the original name in the source *)
  is_generated : bool;
}

type var_ident = ident

let num = ref 0

let ident_compare id1 id2 = compare id1.num id2.num
let sourcename id = id.source
let name id =
  if id.is_generated then
    id.source ^ "_" ^ (string_of_int id.num)
  else
    id.source

let set_sourcename id v =
  { id with source = v }

let fprint_t ff id = Format.fprintf ff "%s" (name id)

module M = struct
  type t = ident
  let compare = ident_compare
  let fprint = fprint_t
end

module Env =
struct
  include (Map.Make(M))

  let append env0 env =
    fold (fun key v env -> add key v env) env0 env

  (* Environments union *)
  let union env1 env2 =
    fold (fun name elt env -> add name elt env) env2 env1

  (* Environments difference : env1 - env2 *)
  let diff env1 env2 =
    fold (fun name _ env -> remove name env) env2 env1

  (* Environments partition *)
  let partition p env =
    fold
      (fun key elt (env1,env2) ->
         if p(key)
         then ((add key elt env1),env2)
         else (env1,(add key elt env2)))
      env
      (empty, empty)
end

module IdentSet = struct
  include (Set.Make(M))

  let fprint_t ff s =
    Format.fprintf ff "@[<hov>{@ ";
    iter (fun e -> Format.fprintf ff "%a@ " M.fprint e) s;
    Format.fprintf ff "}@]";
end

module S = Set.Make (struct type t = string
                            let compare = Pervasives.compare end)

module UniqueNames =
struct
  let used_names = ref S.empty
  let env = ref Env.empty

  let new_function () =
    used_names := S.empty

  (** @return a unique string for each identifier. Idents corresponding
      to variables defined in the source file have the same name unless
      there is a collision. *)
  let assign_name n =
    let fresh s =
      num := !num + 1;
      s ^ "_" ^ (string_of_int !num)
    in
    let rec fresh_string base =
      let base = fresh base in
        if S.mem base !used_names then fresh_string base else base
    in
      if not (Env.mem n !env) then
        let s = name n in
        let s = if S.mem s !used_names then fresh_string s else s in
          used_names := S.add s !used_names;
          env := Env.add n s !env

  let name id =
    Env.find id !env
end

let fresh s =
  num := !num + 1;
  let id = { num = !num; source = s; is_generated = true } in
    UniqueNames.assign_name id; id

let ident_of_name s =
  num := !num + 1;
  let id = { num = !num; source = s; is_generated = false } in
    UniqueNames.assign_name id; id

let name id = UniqueNames.name id
let new_function () = UniqueNames.new_function ()

let print_ident ff id = Format.fprintf ff "%s" (name id)
