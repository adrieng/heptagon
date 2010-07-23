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

let compare id1 id2 = compare id1.num id2.num
let sourcename id = id.source
let name id =
  if id.is_generated then
    id.source ^ "_" ^ (string_of_int id.num)
  else
    id.source

let set_sourcename id v =
  { id with source = v }

let num = ref 0
let fresh s =
  num := !num + 1;
  { num = !num; source = s; is_generated = true }

let ident_of_name s =
  num := !num + 1;
  { num = !num; source = s; is_generated = false }

let fprint_t ff id = Format.fprintf ff "%s" (name id)

module M = struct
  type t = ident
  let compare = compare
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


let print_ident ff id = Format.fprintf ff "%s" (name id)
