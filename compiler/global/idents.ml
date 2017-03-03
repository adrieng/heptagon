(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)

(* naming and local environment *)

(* TODO AG : preprocessing pour avoir un release efficace :
IFDEF RELEASE type iden = int
ELSE *)



type ident = {
  num : int;        (* a unique index *)
  source : string;  (* the original name in the source *)
  is_generated : bool;
  is_reset : bool;
}

let is_reset id = id.is_reset

type var_ident = ident

let num = ref 0

let ident_compare id1 id2 = compare id1.num id2.num

(* used only for debuging *)
let name id =
  if id.is_generated then
    id.source ^ "_" ^ (string_of_int id.num)
  else
    id.source

(* used only for debuging *)
let print_ident ff id = Format.fprintf ff "%s" (name id)

module M = struct
  type t = ident
  let compare = ident_compare
  let print_t = print_ident
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

  (* Print Env *)
  let print_t print_value ff m =
    Format.fprintf ff "@[<hov>{@ ";
    iter (fun k v -> Format.fprintf ff "%a => %a,@ " M.print_t k print_value v) m;
    Format.fprintf ff "}@]";
end

module IdentSet = struct
  include (Set.Make(M))

  let print_t ff s =
    Format.fprintf ff "@[<hov>{@ ";
    iter (fun e -> Format.fprintf ff "%a,@ " M.print_t e) s;
    Format.fprintf ff "}@]";
end

module S = Set.Make (struct type t = string
                            let compare = Pervasives.compare end)


(** Module used to generate unique string (inside a node) per ident.
    /!\ Any pass generating a name must call [enter_node] and use gen_fresh *)
module UniqueNames =
struct
  open Names

  (** Used strings in the current node *)
  let used_names = ref (ref NamesSet.empty)

  (** Map idents to their string *)
  let env = ref Env.empty
  let (node_env : NamesSet.t ref QualEnv.t ref) = ref QualEnv.empty
  let name_counters = Hashtbl.create 500

  (** This function should be called every time we enter a node *)
  let enter_node n =
    (* TODO : see copy_node; same problem *)
    (if not (QualEnv.mem n !node_env)
    then node_env := QualEnv.add n (ref NamesSet.empty) !node_env);
    used_names := QualEnv.find n !node_env

  (** Copy environment of node of name [n] to new node name [n'] *)
  let copy_node n n' =
    (* TODO : do something smarter than create empty used names set *)
    (* this happen when an object file is loaded: the used names set
       of loaded nodes is not properly set *)
    if not (QualEnv.mem n !node_env)
    then node_env := QualEnv.add n (ref NamesSet.empty) !node_env;
    assert (not (QualEnv.mem n' !node_env));
    let used_names = !(QualEnv.find n !node_env) in
    node_env := QualEnv.add n' (ref used_names) !node_env

  (** @return a unique string for each identifier. Idents corresponding
      to variables defined in the source file have the same name unless
      there is a collision. *)
  let assign_name n =

    let find_and_increment_counter s =
      let num = try Hashtbl.find name_counters s with Not_found -> 1 in
      Hashtbl.add name_counters s (num + 1);
      num
    in

    let rec fresh_string s =
      let num = find_and_increment_counter s in
      let new_name = s ^ "_" ^ string_of_int num in
      if NamesSet.mem new_name !(!used_names) then fresh_string s else new_name
    in

    if not (Env.mem n !env) then
      (let s = n.source in
       let s = if NamesSet.mem s !(!used_names) then fresh_string s else s in
       !used_names := NamesSet.add s !(!used_names);
       env := Env.add n s !env)

  let name id =
    Env.find id !env
end

let gen_fresh pass_name kind_to_string ?(reset=false) kind =
  let s = kind_to_string kind in
  let s = if !Compiler_options.full_name then "__"^pass_name ^ "_" ^ s else s in
  num := !num + 1;
  let id = { num = !num; source = s; is_generated = true; is_reset = reset } in
    UniqueNames.assign_name id; id

let gen_var pass_name ?(reset=false) name =
  gen_fresh pass_name (fun () -> name) ~reset:reset ()

let ident_of_name ?(reset=false) s =
  num := !num + 1;
  let id = { num = !num; source = s; is_generated = false; is_reset = reset } in
    UniqueNames.assign_name id; id

let source_name id = id.source
let name id = UniqueNames.name id
let enter_node n = UniqueNames.enter_node n
let copy_node = UniqueNames.copy_node

let print_ident ff id = Format.fprintf ff "%s" (name id)
