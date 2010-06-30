open Misc
open Minils
open Names
open Ident
open Format
open Location
open Printf
open Static
open Signature

let nodes_instances = ref NamesEnv.empty
let global_env = ref NamesEnv.empty

let rec string_of_int_list = function
  | [] -> ""
  | [n] -> (string_of_int n)
  | n::l -> (string_of_int n)^", "^(string_of_int_list l)

let add_node_params n params =
  if NamesEnv.mem n !nodes_instances then
    nodes_instances := NamesEnv.add n
      (params::(NamesEnv.find n !nodes_instances)) !nodes_instances
  else
    nodes_instances := NamesEnv.add n [params] !nodes_instances

let rec node_by_name s = function
  | [] -> raise Not_found
  | n::l ->
      if n.n_name = s then
        n
      else
        node_by_name s l

let build env params_names params_values =
  List.fold_left2 (fun m { p_name = n } v -> NamesEnv.add n (SConst v) m)
    env params_names params_values

let rec collect_exp nodes env e =
  match e.e_desc with
    | Emerge(_, c_e_list) ->
        List.iter (fun (_, e) -> collect_exp nodes env e) c_e_list
    | Eifthenelse(e1, e2, e3) ->
        collect_exp nodes env e1;
        collect_exp nodes env e2;
        collect_exp nodes env e3
    | Ewhen(e, _, _) | Efby(_, e) | Efield(e, _) ->
        collect_exp nodes env e
    | Evar _ | Econstvar _ | Econst _ -> ()
    | Estruct(f_e_list) ->
        List.iter (fun (_, e) -> collect_exp nodes env e) f_e_list
    | Etuple e_list | Earray e_list ->
        List.iter (collect_exp nodes env) e_list
    | Efield_update(_, e1, e2) ->
        collect_exp nodes env e1;
        collect_exp nodes env e2
    (* Do the real work: call node *)
    | Ecall( { op_name = ln; op_params = params; op_kind = _ },
             e_list, _) ->
        List.iter (collect_exp nodes env) e_list;
        let params = List.map (int_of_size_exp env) params in
        call_node_instance nodes ln params
    | Earray_op op ->
        collect_array_exp nodes env op

and collect_array_exp nodes env = function
  | Eselect_dyn (e_list, _, e1, e2) ->
      List.iter (collect_exp nodes env) e_list;
      collect_exp nodes env e1;
      collect_exp nodes env e2
  | Eupdate (_, e1, e2) | Econcat (e1, e2) ->
      collect_exp nodes env e1;
      collect_exp nodes env e2
  | Eselect (_,e) | Eselect_slice (_ , _, e) | Erepeat (_,e)  ->
      collect_exp nodes env e
  | Eiterator (_, { op_name = ln; op_params = params }, _, e_list, _) ->
      List.iter (collect_exp nodes env) e_list;
      let params = List.map (int_of_size_exp env) params in
      call_node_instance nodes ln params

and collect_eqs nodes env eq =
  collect_exp nodes env eq.eq_rhs

and call_node_instance nodes ln params =
  match params with
    | [] -> ()
    | params ->
        let n = node_by_name (shortname ln) nodes in
        node_call nodes n params

and node_call nodes n params =
  match params with
    | [] ->
        List.iter (collect_eqs nodes !global_env) n.n_equs
    | params ->
        add_node_params n.n_name params;
        let env = build !global_env n.n_params params in
        List.iter (collect_eqs nodes env) n.n_equs

let node n =
  let inst =
    if NamesEnv.mem n.n_name !nodes_instances then
      NamesEnv.find n.n_name !nodes_instances
    else
      [] in
  { n with n_params_instances = inst }

let build_const_env cd_list =
  List.fold_left (fun env cd -> NamesEnv.add
                    cd.Minils.c_name cd.Minils.c_value env)
    NamesEnv.empty cd_list

let program p =
  let try_call_node n =
    match n.n_params with
      | [] -> node_call p.p_nodes n []
      | _ -> ()
  in
  global_env := build_const_env p.p_consts;
  List.iter try_call_node p.p_nodes;
  { p with p_nodes = List.map node p.p_nodes }

