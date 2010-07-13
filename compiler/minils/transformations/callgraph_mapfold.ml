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

module Error =
struct
  type error =
    | Enode_unbound of longname
    | Evar_unbound of name

  let message loc kind =
    begin match kind with
      | Enode_unbound ln ->
          Printf.eprintf "%aUnknown node '%s'\n"
            output_location loc
            (fullname ln)
      | Evar_unbound n ->
          Printf.eprintf "%aUnbound static var '%s'\n"
            output_location loc
            n
    end;
    raise Misc.Error
end

type info =
  { mutable opened : program NamesEnv.t;
    mutable called_nodes : ((longname * static_exp list) list) LongNameEnv.t;
    mutable nodes_instances : (static_exp list list) LongNameEnv.t;
    mutable nodes_names : (longname * static_exp list, longname) Hashtbl.t }

let info =
  { opened = NamesEnv.empty;
    called_nodes = LongNameEnv.empty;
    nodes_instances =  LongNameEnv.empty;
    nodes_names = Hashtbl.create 100 }

let load_object_file modname =
  let name = String.uncapitalize modname in
    try
      let filename = Modules.findfile (name ^ ".epo") in
      let ic = open_in_bin filename in
        try
          let p:program = input_value ic in
            if p.p_format_version <> minils_format_version then (
              Printf.eprintf "The file %s was compiled with \
                       an older version of the compiler.\n \
                       Please recompile %s.ept first.\n" filename name;
              raise Error
            );
            close_in ic;
            info.opened <- NamesEnv.add p.p_modname p info.opened
        with
          | End_of_file | Failure _ ->
              close_in ic;
              Printf.eprintf "Corrupted object file %s.\n\
                        Please recompile %s.ept first.\n" filename name;
              raise Error
    with
      | Modules.Cannot_find_file(filename) ->
          Printf.eprintf "Cannot find the object file '%s'.\n"
            filename;
          raise Error

let node_by_longname ln =
  match ln with
    | Modname { qual = q; id = id } ->
        if not (NamesEnv.mem q info.opened) then
          load_object_file q;
        (try
           let p = NamesEnv.find q info.opened in
             List.find (fun n -> n.n_name = id) p.p_nodes
         with
             Not_found -> Error.message no_location (Error.Enode_unbound ln))
    | _ -> assert false

let collect_node_calls ln =
  let edesc funs acc ed = match ed with
    | Eapp ({ a_op = (Enode ln | Efun ln); a_params = params }, _, _) ->
        ed, (ln, params)::acc
    | _ -> raise Misc.Fallback
  in
  let funs = { Mls_mapfold.mls_funs_default with
                 edesc = edesc } in
  let n = node_by_longname ln in
  let _, acc = Mls_mapfold.node_dec funs [] n in
    acc

let called_nodes ln =
  if not (LongNameEnv.mem ln info.called_nodes) then (
    let called = collect_node_calls ln in
      info.called_nodes <- LongNameEnv.add ln called info.called_nodes;
      called
  ) else
    LongNameEnv.find ln info.called_nodes

let add_node_instance ln params =
  if LongNameEnv.mem ln info.nodes_instances then
    info.nodes_instances <- LongNameEnv.add ln
      (params::(LongNameEnv.find ln info.nodes_instances)) info.nodes_instances
  else
    info.nodes_instances <- LongNameEnv.add ln [params] info.nodes_instances

let get_node_instances ln =
  try
    LongNameEnv.find ln info.nodes_instances
  with
      Not_found -> []

let node_for_params_call ln params =
  match params with
    | [] -> ln
    | _ -> Hashtbl.find info.nodes_names (ln,params)

let build env params_names params_values =
  List.fold_left2 (fun m { p_name = n } v -> NamesEnv.add n v m)
    env params_names params_values

module Instantiate =
struct
  let static_exp funs m se = match se.se_desc with
    | Svar ln ->
        let se = (match ln with
           | Name n ->
               (try NamesEnv.find n m
                with Not_found ->
                      Error.message no_location (Error.Evar_unbound n))
           | Modname _ -> se) in
          se, m
    | _ -> raise Misc.Fallback

  let edesc funs m ed =
    let ed, _ = Mls_mapfold.edesc funs m ed in
    let ed = match ed with
        | Eapp ({ a_op = Efun ln; a_params = params } as app, e_list, r) ->
            Eapp ({ app with a_op = Efun (node_for_params_call ln params);
                      a_params = [] }, e_list, r)
        | Eapp ({ a_op = Enode ln; a_params = params } as app, e_list, r) ->
            Eapp ({ app with a_op = Enode (node_for_params_call ln params);
                      a_params = [] }, e_list, r)
        | _ -> ed
    in ed, m

  let generate_new_name ln params =
    match params with
      | [] -> ln
      | _ ->
          (match ln with
             | Modname { qual = q; id = id } ->
                 let new_ln =
                   Modname { qual = q;
                             id = id ^ (Ident.name (Ident.fresh "")) } in
                   Hashtbl.add info.nodes_names (ln, params) new_ln;
                   new_ln
             | _ -> assert false)

  let node_dec_instance modname n params =
    let global_funs = { global_funs_default with
                          static_exp = static_exp } in
    let funs = { Mls_mapfold.mls_funs_default with
                   edesc = edesc;
                   global_funs = global_funs } in
    let m = build NamesEnv.empty n.n_params params in
    let n, _ = Mls_mapfold.node_dec_it funs m n in

    let ln = Modname { qual = modname; id = n.n_name } in
    let { info = node_sig } = find_value ln in
    let node_sig, _ = Global_mapfold.node_it global_funs m node_sig in
    let ln = generate_new_name ln params in
      Modules.add_value_by_longname ln node_sig;
      n

  let node_dec modname n =
    let ln = Modname { qual = modname; id = n.n_name } in
    List.map (node_dec_instance modname n) (get_node_instances ln)

  let program p =
    { p with p_nodes = List.flatten (List.map (node_dec p.p_modname) p.p_nodes) }
end

let check_no_static_var se =
  let static_exp_desc funs acc sed = match sed with
    | Svar (Name n) -> Error.message se.se_loc (Error.Evar_unbound n)
    | _ -> raise Misc.Fallback
  in
  let funs = { Global_mapfold.global_funs_default with
                 static_exp_desc = static_exp_desc } in
  ignore (Global_mapfold.static_exp_it funs false se)


let rec call_node (ln, params) =
  let n = node_by_longname ln in
  let m = build NamesEnv.empty n.n_params params in
  let params = List.map (simplify m) params in
    List.iter check_no_static_var params;
    add_node_instance ln params;

    let call_list = called_nodes ln in
    let call_list = List.map
      (fun (ln, p) -> ln, List.map (static_exp_subst m) p) call_list in
      List.iter call_node call_list

let program p =
  let main_nodes = List.filter (fun n -> is_empty n.n_params) p.p_nodes in
  let main_nodes = List.map (fun n -> (longname n.n_name, [])) main_nodes in
    info.opened <- NamesEnv.add p.p_modname p NamesEnv.empty;
    List.iter call_node main_nodes;
    let p_list = NamesEnv.fold (fun _ p l -> p::l) info.opened [] in
      List.map Instantiate.program p_list
