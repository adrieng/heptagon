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
open Names
open Types
open Misc
open Location
open Signature
open Modules
open Static
open Global_mapfold
open Mls_mapfold
open Minils
open Global_printer

module Error =
struct
  type error =
    | Enode_unbound of qualname
    | Epartial_evaluation of static_exp list

  let message loc kind =
    begin match kind with
      | Enode_unbound ln ->
          Format.eprintf "%aUnknown node '%s'@."
            print_location loc
            (fullname ln)
      | Epartial_evaluation se_l ->
          Format.eprintf "%aUnable to fully instanciate the static exps '%a'@."
            print_location loc
            print_static_exp_tuple se_l
    end;
    raise Errors.Error
end

module Param_instances :
sig
  (** Fully instantiated param *)
  type key = private static_exp
  type env = key QualEnv.t
  val instantiate: env -> static_exp list -> key list
  val get_node_instances : QualEnv.key -> key list list
  val add_node_instance : QualEnv.key -> key list -> unit
  val build : env -> param list -> key list -> env
  module Instantiate :
  sig
    val program : program -> program
  end
end =
struct
  type key = static_exp
  type env = key QualEnv.t

  (** An instance is a list of instantiated params *)
  type instance = key list

  (** two instances are equal if the desc of keys are equal *)
  let compare_instances =
    let compare se1 se2 = compare se1.se_desc se2.se_desc in
    Misc.list_compare compare

  (** Instances set *)
  module S =
    Set.Make(
      struct
        type t = instance
        let compare = compare_instances
      end)

  (** Map instance to its instantiated node *)
  module M =
    Map.Make(
      struct
        type t = qualname * instance
        let compare (l1,i1) (l2,i2) =
          let cl = compare l1 l2 in
          if cl = 0 then compare_instances i1 i2 else cl
      end)

  (** Maps a couple (node name, params) to the name of the instantiated node *)
  let nodes_names = ref M.empty

  (** Maps a node to its list of instances *)
  let nodes_instances = ref QualEnv.empty

  (** create a params instance *)
  let instantiate m se_l =
    try List.map (eval m) se_l
    with Errors.Error ->
      Error.message no_location (Error.Epartial_evaluation se_l)

  (** @return the name of the node corresponding to the instance of
      [ln] with the static parameters [params]. *)
  let node_for_params_call ln params = match params with
    | [] -> ln
    | _ -> let ln = M.find (ln,params) !nodes_names in ln

  (** Generates a fresh name for the the instance of
      [ln] with the static parameters [params] and stores it. *)
  let generate_new_name ln params = match params with
    | [] -> nodes_names := M.add (ln, params) ln !nodes_names
    | _ ->
        let { qual = q; name = n } = ln in
        let param_string =
          List.fold_left
            (fun s se ->
              s ^ (Names.print_pp_to_name Global_printer.print_static_exp se))
            "_params_" params in
        let new_ln =
          Modules.fresh_value_in "callgraph" (n^param_string^"_") q in
        Idents.copy_node ln new_ln;
        nodes_names := M.add (ln, params) new_ln !nodes_names

  (** Adds an instance of a node. *)
  let add_node_instance ln params =
    (* get the already defined instances *)
    let instances = try QualEnv.find ln !nodes_instances
                    with Not_found -> S.empty in
    if S.mem params instances then () (* nothing to do *)
    else ( (* it's a new instance *)
      let instances = S.add params instances in
      nodes_instances := QualEnv.add ln instances !nodes_instances;
      generate_new_name ln params )

  (** @return the list of instances of a node. *)
  let get_node_instances ln =
   let instances_set =
      try QualEnv.find ln !nodes_instances
      with Not_found -> S.empty in
   S.elements instances_set


  (** Build an environment by instantiating the passed params *)
  let build env params_names params_values =
    List.fold_left2 (fun m { p_name = n } v -> QualEnv.add (local_qn n) v m)
      env params_names (instantiate env params_values)


  (** This module creates an instance of a node with a given
      list of static parameters. *)
  module Instantiate =
  struct
    (** Replaces static parameters with their value in the instance. *)
    let static_exp funs m se =
      let se, _ = Global_mapfold.static_exp funs m se in
      let se = match se.se_desc with
        | Svar q ->
            (match q.qual with
              | LocalModule -> (* This var is a static parameter, it has to be instanciated *)
                (try QualEnv.find q m
                 with Not_found -> Misc.internal_error "callgraph")
              | _ -> se)
        | _ -> se in
      se, m

    (** Replaces nodes call with the call to the correct instance. *)
    let edesc funs m ed =
      let ed, _ = Mls_mapfold.edesc funs m ed in
      let ed = match ed with
        | Eapp ({ a_op = Efun ln; a_params = params } as app, e_list, r) ->
            let op = Efun (node_for_params_call ln (instantiate m params)) in
            Eapp ({ app with a_op = op; a_params = [] }, e_list, r)
        | Eapp ({ a_op = Enode ln; a_params = params } as app, e_list, r) ->
            let op = Enode (node_for_params_call ln (instantiate m params)) in
            Eapp ({ app with a_op = op; a_params = [] }, e_list, r)
        | Eiterator(it, ({ a_op = Efun ln; a_params = params } as app),
                      n, pe_list, e_list, r) ->
            let op = Efun (node_for_params_call ln (instantiate m params)) in
            Eiterator(it, {app with a_op = op; a_params = [] },
                     n, pe_list, e_list, r)
        | Eiterator(it, ({ a_op = Enode ln; a_params = params } as app),
                     n, pe_list, e_list, r) ->
            let op = Enode (node_for_params_call ln (instantiate m params)) in
            Eiterator(it,{app with a_op = op; a_params = [] },
                     n, pe_list, e_list, r)
        | _ -> ed
      in ed, m

    let node_dec_instance n params =
      Idents.enter_node n.n_name;
      let global_funs =
        { Global_mapfold.defaults with static_exp = static_exp } in
      let funs =
        { Mls_mapfold.defaults with edesc = edesc;
                                    global_funs = global_funs } in
      let m = build QualEnv.empty n.n_params params in
      let n, _ = Mls_mapfold.node_dec_it funs m n in

      (* Add to the global environment the signature of the new instance *)
      let node_sig = find_value n.n_name in
      let node_sig, _ = Global_mapfold.node_it global_funs m node_sig in
      let node_sig = { node_sig with node_params = [];
                                     node_param_constraints = [] } in
      (* Find the name that was associated to this instance *)
      let ln = node_for_params_call n.n_name params in
        if not (check_value ln) then
          Modules.add_value ln node_sig;
      { n with n_name = ln; n_params = []; n_param_constraints = []; }

    let node_dec n =
      List.map (node_dec_instance n) (get_node_instances n.n_name)

    let program p =
      let program_desc pd acc = match pd with
        | Pnode n ->
            let nds = node_dec n in
            List.fold_left (fun pds n -> Pnode n :: pds) acc nds
        | _ -> pd :: acc
      in
      { p with p_desc = List.fold_right program_desc p.p_desc [] }
  end

end

open Param_instances

type info = {
    mutable opened : program ModulEnv.t; (** Opened programs *)
    mutable called_nodes : ((qualname * static_exp list) list) QualEnv.t;
    (** Maps a node to the list of (node name, params) it calls *)
  }

let info =
  {
    opened = ModulEnv.empty;
    called_nodes = QualEnv.empty
  }

(** Loads the modname.epo file. *)
let load_object_file modul =
  Modules.open_module modul;
  let modname = match modul with
      | Names.Pervasives -> "Pervasives"
      | Names.Module n -> n
      | Names.LocalModule -> Misc.internal_error "modules"
      | Names.QualModule _ -> Misc.unsupported "modules"
  in
  let name = String.uncapitalize_ascii modname in
    try
      let filename = Compiler_utils.findfile (name ^ ".epo") in
      let ic = open_in_bin filename in
        try
          let (p : program) = input_value ic in
            if p.p_format_version <> minils_format_version then (
              Format.eprintf "The file %s was compiled with \
                       an older version of the compiler.@\n\
                       Please recompile %s.ept first.@." filename name;
              raise Errors.Error
            );
            close_in ic;
            info.opened <- ModulEnv.add p.p_modname p info.opened
        with
          | End_of_file | Failure _ ->
              close_in ic;
              Format.eprintf "Corrupted object file %s.@\n\
                        Please recompile %s.ept first.@." filename name;
              raise Errors.Error
    with
      | Compiler_utils.Cannot_find_file(filename) ->
          Format.eprintf "Cannot find the object file '%s'.@."
            filename;
          raise Errors.Error

(** @return the node with name [ln], loading the corresponding
    object file if necessary. *)
let node_by_longname node =
  if not (ModulEnv.mem node.qual info.opened)
  then load_object_file node.qual;
  try
    let p = ModulEnv.find node.qual info.opened in
    let n = List.find (function Pnode n -> n.n_name = node | _ -> false) p.p_desc in
    (match n with
      | Pnode n -> n
      | _ -> Misc.internal_error "callgraph")
  with
    Not_found -> Error.message no_location (Error.Enode_unbound node)

(** @return the list of nodes called by the node named [ln], with the
    corresponding params (static parameters appear as free variables). *)
let collect_node_calls ln =
  (* only add nodes when not external and with params *)
  let add_called_node ln params acc =
    match params with
      | [] -> acc
      | _ ->
        if (Modules.find_value ln).node_external
        then acc
        else (ln, params)::acc
  in
  let edesc _ acc ed = match ed with
    | Eapp ({ a_op = (Enode ln | Efun ln); a_params = params }, _, _) ->
        ed, add_called_node ln params acc
    | Eiterator(_, { a_op = (Enode ln | Efun ln); a_params = params },
                _, _, _, _) ->
        ed, add_called_node ln params acc
    | _ -> raise Errors.Fallback
  in
  let funs = { Mls_mapfold.defaults with edesc = edesc } in
  let n = node_by_longname ln in
  let _, acc = Mls_mapfold.node_dec funs [] n in
  acc

(** @return the list of nodes called by the node named [ln]. This list is
    computed lazily the first time it is needed. *)
let called_nodes ln =
  if not (QualEnv.mem ln info.called_nodes) then (
    let called = collect_node_calls ln in
      info.called_nodes <- QualEnv.add ln called info.called_nodes;
      called
  ) else
    QualEnv.find ln info.called_nodes

(** Generates the list of instances of nodes needed to call
    [ln] with static parameters [params]. *)
let rec call_node (ln, params) =
  (* First, add the instance for this node *)
  let n = node_by_longname ln in
  let m = build QualEnv.empty n.n_params params in
(*  List.iter check_no_static_var params; *)
  add_node_instance ln params;

  (* Recursively generate instances for called nodes. *)
  let call_list = called_nodes ln in
  let call_list =
    List.map (fun (ln, p) -> ln, instantiate m p) call_list in
  List.iter call_node call_list

let program p =
  (* Find the nodes without static parameters *)
  let main_nodes = List.filter (function Pnode n -> is_empty n.n_params | _ -> false) p.p_desc in
  let main_nodes = List.map (function Pnode n -> n.n_name, []
                              | _ -> Misc.internal_error "callgraph") main_nodes in
  info.opened <- ModulEnv.add p.p_modname p ModulEnv.empty;
  (* Creates the list of instances starting from these nodes *)
  List.iter call_node main_nodes;
  let p_list = ModulEnv.fold (fun _ p l -> p::l) info.opened [] in
  (* Generate all the needed instances *)
  List.map Param_instances.Instantiate.program p_list
