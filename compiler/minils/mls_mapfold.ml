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

(* /!\ do not ever, NEVER put in your funs record one
  of the generic iterator function (_it),
  either yours either the default version named according to the type. *)

type 'a mls_it_funs = {
  app:           'a mls_it_funs -> 'a -> Minils.app -> Minils.app * 'a;
  edesc:         'a mls_it_funs -> 'a -> Minils.edesc -> Minils.edesc * 'a;
  eq:            'a mls_it_funs -> 'a -> Minils.eq -> Minils.eq * 'a;
  eqs:           'a mls_it_funs -> 'a -> Minils.eq list -> Minils.eq list * 'a;
  exp:           'a mls_it_funs -> 'a -> Minils.exp -> Minils.exp * 'a;
  extvalue:      'a mls_it_funs -> 'a -> Minils.extvalue -> Minils.extvalue * 'a;
  extvalue_desc: 'a mls_it_funs -> 'a -> Minils.extvalue_desc -> Minils.extvalue_desc * 'a;
  pat:           'a mls_it_funs -> 'a -> Minils.pat -> Minils.pat * 'a;
  var_dec:       'a mls_it_funs -> 'a -> Minils.var_dec -> Minils.var_dec * 'a;
  var_decs:      'a mls_it_funs -> 'a -> Minils.var_dec list -> Minils.var_dec list * 'a;
  contract:      'a mls_it_funs -> 'a -> Minils.contract -> Minils.contract * 'a;
  node_dec:      'a mls_it_funs -> 'a -> Minils.node_dec -> Minils.node_dec * 'a;
  const_dec:     'a mls_it_funs -> 'a -> Minils.const_dec -> Minils.const_dec * 'a;
  type_dec:      'a mls_it_funs -> 'a -> Minils.type_dec -> Minils.type_dec * 'a;
  tdesc:         'a mls_it_funs -> 'a -> Minils.tdesc -> Minils.tdesc * 'a;
  program:       'a mls_it_funs -> 'a -> Minils.program -> Minils.program * 'a;
  program_desc:  'a mls_it_funs -> 'a -> Minils.program_desc -> Minils.program_desc * 'a;
  global_funs:   'a Global_mapfold.global_it_funs }


let rec exp_it funs acc e = funs.exp funs acc e
and exp funs acc e =
  let e_ty, acc = ty_it funs.global_funs acc e.e_ty in
  let ed, acc = edesc_it funs acc e.e_desc in
  { e with e_desc = ed; e_ty = e_ty }, acc

and extvalue_it funs acc w = funs.extvalue funs acc w
and extvalue funs acc w =
  let w_ty, acc = ty_it funs.global_funs acc w.w_ty in
  let wd, acc = extvalue_desc_it funs acc w.w_desc in
  { w with w_desc = wd; w_ty = w_ty }, acc

and extvalue_desc_it funs acc wd =
  try funs.extvalue_desc funs acc wd
  with Fallback -> extvalue_desc funs acc wd
and extvalue_desc funs acc wd = match wd with
  | Wconst se ->
      let se, acc = static_exp_it funs.global_funs acc se in
      Wconst se, acc
  | Wvar _ -> wd, acc
  | Wfield (w,f) ->
      let w, acc = extvalue_it funs acc w in
      Wfield (w,f), acc
  | Wwhen (w, c, v) ->
      let w, acc = extvalue_it funs acc w in
      Wwhen (w,c,v), acc
  | Wreinit (w1, w2) ->
      let w1, acc = extvalue_it funs acc w1 in
      let w2, acc = extvalue_it funs acc w2 in
      Wreinit (w1, w2), acc

and edesc_it funs acc ed =
  try funs.edesc funs acc ed
  with Fallback -> edesc funs acc ed
and edesc funs acc ed = match ed with
  | Eextvalue w ->
      let w, acc = extvalue_it funs acc w in
      Eextvalue w, acc
  | Efby (se, w) ->
      let se, acc = optional_wacc (static_exp_it funs.global_funs) acc se in
      let w, acc = extvalue_it funs acc w in
        Efby (se, w), acc
  | Eapp(app, args, reset) ->
      let app, acc = app_it funs acc app in
      let args, acc = mapfold (extvalue_it funs) acc args in
        Eapp (app, args, reset), acc
  | Emerge(x, c_w_list) ->
      let aux acc (c,w) =
        let w, acc = extvalue_it funs acc w in
          (c,w), acc in
      let c_w_list, acc = mapfold aux acc c_w_list in
        Emerge(x, c_w_list), acc
  | Ewhen(e,c,x) ->
      let e, acc = exp_it funs acc e in
      Ewhen(e,c,x), acc
  | Estruct n_w_list ->
      let aux acc (n,w) =
        let w, acc = extvalue_it funs acc w in
          (n,w), acc in
      let n_w_list, acc = mapfold aux acc n_w_list in
        Estruct n_w_list, acc
  | Eiterator (i, app, params, pargs, args, reset) ->
      let app, acc = app_it funs acc app in
      let params, acc = mapfold (static_exp_it funs.global_funs) acc params in
      let pargs, acc = mapfold (extvalue_it funs) acc pargs in
      let args, acc = mapfold (extvalue_it funs) acc args in
        Eiterator (i, app, params, pargs, args, reset), acc


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
  let c_assume, acc = extvalue_it funs acc c.c_assume in
  let c_enforce, acc = extvalue_it funs acc c.c_enforce in
  let c_local, acc = var_decs_it funs acc c.c_local in
  let c_eq, acc = eqs_it funs acc c.c_eq in
  { c with
    c_assume = c_assume; c_enforce = c_enforce; c_local = c_local; c_eq = c_eq }
  , acc


and node_dec_it funs acc nd =
  Idents.enter_node nd.n_name;
  funs.node_dec funs acc nd
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
  let p_desc, acc = mapfold (program_desc_it funs) acc p.p_desc in
  { p with p_desc = p_desc }, acc

and program_desc_it funs acc pd =
  try funs.program_desc funs acc pd
  with Fallback -> program_desc funs acc pd
and program_desc funs acc pd = match pd with
  | Pconst cd -> let cd, acc = const_dec_it funs acc cd in Pconst cd, acc
  | Ptype td -> let td, acc = type_dec_it funs acc td in Ptype td, acc
  | Pnode n -> let n, acc = node_dec_it funs acc n in Pnode n, acc


let defaults = {
  app = app;
  edesc = edesc;
  eq = eq;
  eqs = eqs;
  exp = exp;
  extvalue = extvalue;
  extvalue_desc = extvalue_desc;
  pat = pat;
  var_dec = var_dec;
  var_decs = var_decs;
  contract = contract;
  node_dec = node_dec;
  const_dec = const_dec;
  type_dec = type_dec;
  tdesc = tdesc;
  program = program;
  program_desc = program_desc;
  global_funs = Global_mapfold.defaults }
