(** Scoping. Introduces unique indexes for local names and replace global
    names by qualified names *)

open Location
open Types
open Hept_parsetree
open Names
open Ident
open Format
open Printf
open Static

module Error =
struct
  type error =
    | Evar of string
    | Econst_var of string
    | Evariable_already_defined of string
    | Econst_variable_already_defined of string
    | Estatic_exp_expected

  let message loc kind =
    begin match kind with
      | Evar name ->
          eprintf "%aThe value identifier %s is unbound.\n"
            output_location loc
            name
      | Econst_var name ->
          eprintf "%aThe const identifier %s is unbound.\n"
            output_location loc
            name
      | Evariable_already_defined name ->
          eprintf "%aThe variable %s is already defined.\n"
            output_location loc
            name
      | Econst_variable_already_defined name ->
          eprintf "%aThe const variable %s is already defined.\n"
            output_location loc
            name
      | Estatic_exp_expected ->
          eprintf "%aA static expression was expected.\n"
            output_location loc
    end;
    raise Misc.Error
end

module Rename =
struct
  include
    (Map.Make (struct type t = string let compare = String.compare end))
  let append env0 env =
    fold (fun key v env -> add key v env) env0 env

  let name loc env n =
    try
      find n env
    with
        Not_found -> Error.message loc (Error.Evar(n))
end

(*Functions to build the renaming map*)
let add_var loc x env =
  if Rename.mem x env then
    Error.message loc (Error.Evariable_already_defined x)
  else (* create a new id for this var and add it to the env *)
    Rename.add x (ident_of_name x) env

let add_const_var loc x env =
  if NamesEnv.mem x env then
    Error.message loc (Error.Econst_variable_already_defined x)
  else (* create a new id for this var and add it to the env *)
    NamesEnv.add x x env

let rec build_pat loc env = function
  | Evarpat x -> add_var loc x env
  | Etuplepat l ->
      List.fold_left (build_pat loc) env l

let build_vd_list env l =
  let build_vd env vd =
    add_var vd.v_loc vd.v_name env
  in
  List.fold_left build_vd env l

let build_cd_list env l =
  let build_cd env cd =
    add_const_var cd.c_loc cd.c_name env
  in
  List.fold_left build_cd env l

let build_id_list loc env l =
  let build_id env vd =
    add_const_var loc vd.v_name env
  in
  List.fold_left build_id env l

(* Translate the AST into Heptagon. *)
let translate_iterator_type = function
  | Imap -> Heptagon.Imap
  | Ifold -> Heptagon.Ifold
  | Imapfold -> Heptagon.Imapfold

let op_from_app loc app =
  match app.a_op with
    | Efun op | Enode op -> op_from_app_name op
    | _ -> raise Not_static

let rec static_exp_of_exp const_env e =
  let desc = match e.e_desc with
    | Evar n ->
        if NamesEnv.mem n const_env then
          Svar (Name n)
        else
          raise Not_static
    | Econst se -> se.se_desc
    | Eapp({ a_op = Earray_fill }, [e;n]) ->
        Sarray_power (static_exp_of_exp const_env e,
                      static_exp_of_exp const_env n)
    | Eapp({ a_op = Earray }, e_list) ->
        Sarray (List.map (static_exp_of_exp const_env) e_list)
    | Eapp({ a_op = Etuple }, e_list) ->
        Stuple (List.map (static_exp_of_exp const_env) e_list)
    | Eapp(app, e_list) ->
        let op = op_from_app e.e_loc app in
          Sop(op, List.map (static_exp_of_exp const_env) e_list)
    | Estruct e_list ->
        Srecord (List.map (fun (f,e) -> f,
                             static_exp_of_exp const_env e) e_list)
    | _ -> raise Not_static
  in
     mk_static_exp ~loc:e.e_loc desc

let expect_static_exp const_env e =
  try
    static_exp_of_exp const_env e
  with
      Not_static -> Error.message e.e_loc Error.Estatic_exp_expected

let rec translate_type const_env = function
  | Tprod ty_list -> Types.Tprod(List.map (translate_type const_env) ty_list)
  | Tid ln -> Types.Tid ln
  | Tarray (ty, e) ->
      let ty = translate_type const_env ty in
        Types.Tarray (ty, expect_static_exp const_env e)

and translate_exp const_env env e =
  let desc =
    try (* try to see if the exp is a constant *)
      Heptagon.Econst (static_exp_of_exp const_env e)
    with
        Not_static -> translate_desc e.e_loc const_env env e.e_desc in
  { Heptagon.e_desc = desc;
    Heptagon.e_ty = Types.invalid_type;
    Heptagon.e_loc = e.e_loc }

and translate_desc loc const_env env = function
  | Econst c -> Heptagon.Econst c
  | Evar x ->
      if Rename.mem x env then (* defined var *)
        Heptagon.Evar (Rename.name loc env x)
      else if NamesEnv.mem x const_env then (* defined as const var *)
        Heptagon.Econst (mk_static_exp (Svar (Modules.longname x)))
      else (* undefined var *)
        Error.message loc (Error.Evar x)
  | Elast x -> Heptagon.Elast (Rename.name loc env x)
  | Epre (None, e) -> Heptagon.Epre (None, translate_exp const_env env e)
  | Epre (Some c, e) ->
      Heptagon.Epre (Some (expect_static_exp const_env c),
                    translate_exp const_env env e)
  | Efby (e1, e2) -> Heptagon.Efby (translate_exp const_env env e1,
                                    translate_exp const_env env e2)
  | Estruct f_e_list ->
      let f_e_list =
        List.map (fun (f,e) -> f, translate_exp const_env env e) f_e_list in
      Heptagon.Estruct f_e_list
  | Eapp ({ a_op = op; a_params = params }, e_list) ->
      let e_list = List.map (translate_exp const_env env) e_list in
      let params = List.map (expect_static_exp const_env) params in
      let app = Heptagon.mk_op ~params:params (translate_op op) in
        Heptagon.Eapp (app, e_list, None)
  | Eiterator (it, { a_op = op; a_params = params }, n, e_list) ->
      let e_list = List.map (translate_exp const_env env) e_list in
      let n = expect_static_exp const_env n in
      let params = List.map (expect_static_exp const_env) params in
      let app = Heptagon.mk_op ~params:params (translate_op op) in
      Heptagon.Eiterator (translate_iterator_type it,
                          app, n, e_list, None)

and translate_op = function
  | Earrow -> Heptagon.Earrow
  | Eifthenelse -> Heptagon.Eifthenelse
  | Efield -> Heptagon.Efield
  | Efield_update -> Heptagon.Efield_update
  | Etuple -> Heptagon.Etuple
  | Earray -> Heptagon.Earray
  | Eselect -> Heptagon.Eselect
  | Eupdate -> Heptagon.Eupdate
  | Earray_fill -> Heptagon.Earray_fill
  | Eselect_slice -> Heptagon.Eselect_slice
  | Econcat -> Heptagon.Econcat
  | Eselect_dyn -> Heptagon.Eselect_dyn
  | Efun ln -> Heptagon.Efun ln
  | Enode ln -> Heptagon.Enode ln

and translate_pat loc env = function
  | Evarpat x -> Heptagon.Evarpat (Rename.name loc env x)
  | Etuplepat l -> Heptagon.Etuplepat (List.map (translate_pat loc env) l)

let rec translate_eq const_env env eq =
  { Heptagon.eq_desc = translate_eq_desc eq.eq_loc const_env env eq.eq_desc ;
    Heptagon.eq_statefull = false;
    Heptagon.eq_loc = eq.eq_loc }

and translate_eq_desc loc const_env env = function
  | Eswitch(e, switch_handlers) ->
      let sh = List.map
        (translate_switch_handler loc const_env env)
        switch_handlers in
      Heptagon.Eswitch (translate_exp const_env env e, sh)
  | Eeq(p, e) ->
      Heptagon.Eeq (translate_pat loc env p, translate_exp const_env env e)
  | Epresent (present_handlers, b) ->
      Heptagon.Epresent
        (List.map (translate_present_handler const_env env) present_handlers
           , fst (translate_block const_env env b))
  | Eautomaton state_handlers ->
      Heptagon.Eautomaton (List.map (translate_state_handler const_env env)
                             state_handlers)
  | Ereset (eq_list, e) ->
      Heptagon.Ereset (List.map (translate_eq const_env env) eq_list,
                       translate_exp const_env env e)

and translate_block const_env env b =
  let env = build_vd_list env b.b_local in
  { Heptagon.b_local = translate_vd_list const_env env b.b_local;
    Heptagon.b_equs = List.map (translate_eq const_env env) b.b_equs;
    Heptagon.b_defnames = Env.empty ;
    Heptagon.b_statefull = false;
    Heptagon.b_loc = b.b_loc }, env

and translate_state_handler const_env env sh =
  let b, env = translate_block const_env env sh.s_block in
  { Heptagon.s_state = sh.s_state;
    Heptagon.s_block = b;
    Heptagon.s_until = List.map (translate_escape const_env env) sh.s_until;
    Heptagon.s_unless = List.map (translate_escape const_env env) sh.s_unless; }

and translate_escape const_env env esc =
  { Heptagon.e_cond = translate_exp const_env env esc.e_cond;
    Heptagon.e_reset = esc.e_reset;
    Heptagon.e_next_state = esc.e_next_state }

and translate_present_handler const_env env ph =
  { Heptagon.p_cond = translate_exp const_env env ph.p_cond;
    Heptagon.p_block = fst (translate_block const_env env ph.p_block) }

and translate_switch_handler loc const_env env sh =
  { Heptagon.w_name = sh.w_name;
    Heptagon.w_block = fst (translate_block const_env env sh.w_block) }

and translate_var_dec const_env env vd =
  { Heptagon.v_ident = Rename.name vd.v_loc env vd.v_name;
    Heptagon.v_type = translate_type const_env vd.v_type;
    Heptagon.v_last = translate_last const_env env vd.v_last;
    Heptagon.v_loc = vd.v_loc }

and translate_vd_list const_env env =
  List.map (translate_var_dec const_env env)

and translate_last const_env env = function
  | Var -> Heptagon.Var
  | Last (None) -> Heptagon.Last None
  | Last (Some e) -> Heptagon.Last (Some (expect_static_exp const_env e))

let translate_contract const_env env ct =
  { Heptagon.c_assume = translate_exp const_env env ct.c_assume;
    Heptagon.c_enforce = translate_exp const_env env ct.c_enforce;
    Heptagon.c_local = translate_vd_list const_env env ct.c_local;
    Heptagon.c_eq = List.map (translate_eq const_env env) ct.c_eq }

let param_of_var_dec const_env vd =
  Signature.mk_param vd.v_name (translate_type const_env vd.v_type)

let translate_node const_env env node =
  let const_env = build_id_list node.n_loc const_env node.n_params in
  let env = build_vd_list env (node.n_input @ node.n_output @ node.n_local) in
  { Heptagon.n_name = node.n_name;
    Heptagon.n_statefull = node.n_statefull;
    Heptagon.n_input = translate_vd_list const_env env node.n_input;
    Heptagon.n_output = translate_vd_list const_env env node.n_output;
    Heptagon.n_local = translate_vd_list const_env env node.n_local;
    Heptagon.n_contract = Misc.optional
      (translate_contract const_env env) node.n_contract;
    Heptagon.n_equs = List.map (translate_eq const_env env) node.n_equs;
    Heptagon.n_loc = node.n_loc;
    Heptagon.n_params = List.map (param_of_var_dec const_env) node.n_params;
    Heptagon.n_params_constraints = []; }

let translate_typedec const_env ty =
  let onetype = function
    | Type_abs -> Heptagon.Type_abs
    | Type_enum(tag_list) -> Heptagon.Type_enum(tag_list)
    | Type_struct(field_ty_list) ->
        let translate_field_type (f,ty) =
          Signature.mk_field f (translate_type const_env ty) in
        Heptagon.Type_struct (List.map translate_field_type field_ty_list)
  in
  { Heptagon.t_name = ty.t_name;
    Heptagon.t_desc = onetype ty.t_desc;
    Heptagon.t_loc = ty.t_loc }

let translate_const_dec const_env cd =
  { Heptagon.c_name = cd.c_name;
    Heptagon.c_type = translate_type const_env cd.c_type;
    Heptagon.c_value = expect_static_exp const_env cd.c_value;
    Heptagon.c_loc = cd.c_loc; }

let translate_program p =
  let const_env = build_cd_list NamesEnv.empty p.p_consts in
  { Heptagon.p_modname = p.p_modname;
    Heptagon.p_opened = p.p_opened;
    Heptagon.p_types = List.map (translate_typedec const_env) p.p_types;
    Heptagon.p_nodes =
      List.map (translate_node const_env Rename.empty) p.p_nodes;
    Heptagon.p_consts = List.map (translate_const_dec const_env) p.p_consts; }

let translate_arg const_env a =
  Signature.mk_arg a.a_name (translate_type const_env a.a_type)

let translate_signature s =
  let const_env = build_id_list no_location NamesEnv.empty s.sig_params in
  { Heptagon.sig_name = s.sig_name;
    Heptagon.sig_inputs = List.map (translate_arg const_env) s.sig_inputs;
    Heptagon.sig_outputs = List.map (translate_arg const_env) s.sig_outputs;
    Heptagon.sig_statefull = s.sig_statefull;
    Heptagon.sig_params = List.map (param_of_var_dec const_env) s.sig_params; }

let translate_interface_desc const_env = function
  | Iopen n -> Heptagon.Iopen n
  | Itypedef tydec -> Heptagon.Itypedef (translate_typedec const_env tydec)
  | Iconstdef const_dec -> Heptagon.Iconstdef (translate_const_dec const_env const_dec)
  | Isignature s -> Heptagon.Isignature (translate_signature s)

let translate_interface_decl const_env idecl =
  { Heptagon.interf_desc = translate_interface_desc const_env idecl.interf_desc;
    Heptagon.interf_loc = idecl.interf_loc }

let translate_interface =
  List.map (translate_interface_decl NamesEnv.empty)

