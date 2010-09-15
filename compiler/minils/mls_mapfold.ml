 (**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* Generic mapred over Minils Ast *)
open Misc
open Errors
open Global_mapfold
open Minils

(* /!\ do never, never put in your funs record one
  of the generic iterator function (_it),
  either yours either the default version named according to the type. *)

type 'a mls_it_funs = {
  app:        'a mls_it_funs -> 'a -> Minils.app -> Minils.app * 'a;
  edesc:      'a mls_it_funs -> 'a -> Minils.edesc -> Minils.edesc * 'a;
  eq:         'a mls_it_funs -> 'a -> Minils.eq -> Minils.eq * 'a;
  eqs:        'a mls_it_funs -> 'a -> Minils.eq list -> Minils.eq list * 'a;
  exp:        'a mls_it_funs -> 'a -> Minils.exp -> Minils.exp * 'a;
  pat:        'a mls_it_funs -> 'a -> Minils.pat -> Minils.pat * 'a;
  var_dec:    'a mls_it_funs -> 'a -> Minils.var_dec -> Minils.var_dec * 'a;
  var_decs:   'a mls_it_funs -> 'a -> Minils.var_dec list
                                   -> Minils.var_dec list * 'a;
  contract:   'a mls_it_funs -> 'a -> Minils.contract -> Minils.contract * 'a;
  node_dec:   'a mls_it_funs -> 'a -> Minils.node_dec -> Minils.node_dec * 'a;
  const_dec:  'a mls_it_funs -> 'a -> Minils.const_dec -> Minils.const_dec * 'a;
  type_dec:   'a mls_it_funs -> 'a -> Minils.type_dec -> Minils.type_dec * 'a;
  tdesc:      'a mls_it_funs -> 'a -> Minils.tdesc -> Minils.tdesc * 'a;
  program:    'a mls_it_funs -> 'a -> Minils.program -> Minils.program * 'a;
  global_funs:'a Global_mapfold.global_it_funs }


let rec exp_it funs acc e = funs.exp funs acc e
and exp funs acc e =
  let e_ty, acc = ty_it funs.global_funs acc e.e_ty in
  let ed, acc = edesc_it funs acc e.e_desc in
  { e with e_desc = ed; e_ty = e_ty }, acc


and edesc_it funs acc ed =
  try funs.edesc funs acc ed
  with Fallback -> edesc funs acc ed
and edesc funs acc ed = match ed with
  | Econst se ->
      let se, acc = static_exp_it funs.global_funs acc se in
        Econst se, acc
  | Evar x -> ed, acc
  | Efby (se, e) ->
      let se, acc = optional_wacc (static_exp_it funs.global_funs) acc se in
      let e, acc = exp_it funs acc e in
        Efby (se, e), acc
  | Eapp(app, args, reset) ->
      let app, acc = app_it funs acc app in
      let args, acc = mapfold (exp_it funs) acc args in
        Eapp (app, args, reset), acc
  | Ewhen(e, c, x) ->
      let e, acc = exp_it funs acc e in
        Ewhen(e, c, x), acc
  | Emerge(x, c_e_list) ->
      let aux acc (c,e) =
        let e, acc = exp_it funs acc e in
          (c,e), acc in
      let c_e_list, acc = mapfold aux acc c_e_list in
        Emerge(x, c_e_list), acc
  | Estruct n_e_list ->
      let aux acc (n,e) =
        let e, acc = exp_it funs acc e in
          (n,e), acc in
      let n_e_list, acc = mapfold aux acc n_e_list in
        Estruct n_e_list, acc
  | Eiterator (i, app, param, args, reset) ->
      let app, acc = app_it funs acc app in
      let param, acc = static_exp_it funs.global_funs acc param in
      let args, acc = mapfold (exp_it funs) acc args in
        Eiterator (i, app, param, args, reset), acc


and app_it funs acc a = funs.app funs acc a
and app funs acc a =
  let p, acc = mapfold (static_exp_it funs.global_funs) acc a.a_params in
  { a with a_params = p }, acc


and pat_it funs acc p =
  try funs.pat funs acc p
  with Fallback -> pat funs acc p
and pat funs acc p = match p with
  | Etuplepat pl ->
      let pl, acc = mapfold (pat_it funs) acc pl in
      Etuplepat pl, acc
  | Evarpat _ -> p, acc


and eq_it funs acc eq = funs.eq funs acc eq
and eq funs acc eq =
  let eq_lhs, acc = pat_it funs acc eq.eq_lhs in
  let eq_rhs, acc = exp_it funs acc eq.eq_rhs in
    { eq with eq_lhs = eq_lhs; eq_rhs = eq_rhs }, acc

and eqs_it funs acc eqs = funs.eqs funs acc eqs
and eqs funs acc eqs = mapfold (eq_it funs) acc eqs


and var_dec_it funs acc vd = funs.var_dec funs acc vd
and var_dec funs acc vd =
  let v_type, acc = ty_it funs.global_funs acc vd.v_type in
  { vd with v_type = v_type }, acc

and var_decs_it funs acc vds = funs.var_decs funs acc vds
and var_decs funs acc vds = mapfold (var_dec_it funs) acc vds


and contract_it funs acc c = funs.contract funs acc c
and contract funs acc c =
  let c_assume, acc = exp_it funs acc c.c_assume in
  let c_enforce, acc = exp_it funs acc c.c_enforce in
  let c_local, acc = var_decs_it funs acc c.c_local in
  let c_eq, acc = eqs_it funs acc c.c_eq in
  { c with
    c_assume = c_assume; c_enforce = c_enforce; c_local = c_local; c_eq = c_eq }
  , acc


and node_dec_it funs acc nd = funs.node_dec funs acc nd
and node_dec funs acc nd =
  let n_input, acc = var_decs_it funs acc nd.n_input in
  let n_output, acc = var_decs_it funs acc nd.n_output in
  let n_local, acc = var_decs_it funs acc nd.n_local in
  let n_params, acc = mapfold (param_it funs.global_funs) acc nd.n_params in
  let n_contract, acc =  optional_wacc (contract_it funs) acc nd.n_contract in
  let n_equs, acc = eqs_it funs acc nd.n_equs in
  { nd with
      n_input = n_input; n_output = n_output;
      n_local = n_local; n_params = n_params;
      n_contract = n_contract; n_equs = n_equs }
  , acc


and const_dec_it funs acc c = funs.const_dec funs acc c
and const_dec funs acc c =
  let ty, acc = ty_it funs.global_funs acc c.c_type in
  let se, acc = static_exp_it funs.global_funs acc c.c_value in
  { c with c_type = ty; c_value = se }, acc


and type_dec_it funs acc t = funs.type_dec funs acc t
and type_dec funs acc t =
  let tdesc, acc = tdesc_it funs acc t.t_desc in
    { t with t_desc = tdesc }, acc


and tdesc_it funs acc td =
  try funs.tdesc funs acc td
  with Fallback -> tdesc funs acc td
and tdesc funs acc td = match td with
  | Type_struct s ->
      let s, acc = structure_it funs.global_funs acc s in
        Type_struct s, acc
  | Type_alias ty ->
      let ty, acc = ty_it funs.global_funs acc ty in
        Type_alias ty, acc
  | Type_abs | Type_enum _ -> td, acc


and program_it funs acc p = funs.program funs acc p
and program funs acc p =
  let cd_list, acc = mapfold (const_dec_it funs) acc p.p_consts in
  let td_list, acc = mapfold (type_dec_it funs) acc p.p_types in
  let nd_list, acc = mapfold (node_dec_it funs) acc p.p_nodes in
  { p with p_types = td_list; p_consts = cd_list; p_nodes = nd_list }, acc

let defaults = {
  app = app;
  edesc = edesc;
  eq = eq;
  eqs = eqs;
  exp = exp;
  pat = pat;
  var_dec = var_dec;
  var_decs = var_decs;
  contract = contract;
  node_dec = node_dec;
  const_dec = const_dec;
  type_dec = type_dec;
  tdesc = tdesc;
  program = program;
  global_funs = Global_mapfold.defaults }
