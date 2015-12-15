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
  objective:     'a mls_it_funs -> 'a -> Minils.objective -> Minils.objective * 'a;
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
  let e_level_ck, acc = ck_it funs.global_funs acc e.e_level_ck in
  let e_ct, acc = ct_it funs.global_funs acc e.e_ct in
  let ed, acc = edesc_it funs acc e.e_desc in
  { e with e_desc = ed; e_ty = e_ty; e_level_ck = e_level_ck;
           e_ct = e_ct }, acc

and extvalue_it funs acc w = funs.extvalue funs acc w
and extvalue funs acc w =
  let w_ty, acc = ty_it funs.global_funs acc w.w_ty in
  let w_ck, acc = ck_it funs.global_funs acc w.w_ck in
  let wd, acc = extvalue_desc_it funs acc w.w_desc in
  { w with w_desc = wd; w_ty = w_ty; w_ck = w_ck }, acc

and extvalue_desc_it funs acc wd =
  try funs.extvalue_desc funs acc wd
  with Fallback -> extvalue_desc funs acc wd
and extvalue_desc funs acc wd = match wd with
  | Wconst se ->
      let se, acc = static_exp_it funs.global_funs acc se in
      Wconst se, acc
  | Wvar v ->
      let v, acc = var_ident_it funs.global_funs acc v in
      Wvar v, acc
  | Wfield (w,f) ->
      let w, acc = extvalue_it funs acc w in
      Wfield (w,f), acc
  | Wwhen (w, c, v) ->
      let w, acc = extvalue_it funs acc w in
      let v, acc = var_ident_it funs.global_funs acc v in
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
      let reset, acc = optional_wacc (var_ident_it funs.global_funs) acc reset in
      Eapp (app, args, reset), acc
  | Emerge(x, c_w_list) ->
      let aux acc (c,w) =
        let w, acc = extvalue_it funs acc w in
        (c,w), acc
      in
      let c_w_list, acc = mapfold aux acc c_w_list in
      let x, acc = var_ident_it funs.global_funs acc x in
      Emerge(x, c_w_list), acc
  | Ewhen(e,c,x) ->
      let e, acc = exp_it funs acc e in
      let x, acc = var_ident_it funs.global_funs acc x in
      Ewhen(e,c,x), acc
  | Estruct n_w_list ->
      let aux acc (n,w) =
        let w, acc = extvalue_it funs acc w in
        (n,w), acc
      in
      let n_w_list, acc = mapfold aux acc n_w_list in
      Estruct n_w_list, acc
  | Eiterator (i, app, params, pargs, args, reset) ->
      let app, acc = app_it funs acc app in
      let params, acc = mapfold (static_exp_it funs.global_funs) acc params in
      let pargs, acc = mapfold (extvalue_it funs) acc pargs in
      let args, acc = mapfold (extvalue_it funs) acc args in
      let reset, acc = optional_wacc (var_ident_it funs.global_funs) acc reset in
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
  | Evarpat v ->
    let v, acc = var_ident_it funs.global_funs acc v in
    Evarpat v, acc


and eq_it funs acc eq = funs.eq funs acc eq
and eq funs acc eq =
  let eq_lhs, acc = pat_it funs acc eq.eq_lhs in
  let eq_base_ck, acc = ck_it funs.global_funs acc eq.eq_base_ck in
  let eq_rhs, acc = exp_it funs acc eq.eq_rhs in
    { eq with eq_lhs = eq_lhs; eq_rhs = eq_rhs; eq_base_ck = eq_base_ck }, acc

and eqs_it funs acc eqs = funs.eqs funs acc eqs
and eqs funs acc eqs = mapfold (eq_it funs) acc eqs


and var_dec_it funs acc vd = funs.var_dec funs acc vd
and var_dec funs acc vd =
  let v_type, acc = ty_it funs.global_funs acc vd.v_type in
  let v, acc = var_ident_it funs.global_funs acc vd.v_ident in
  let v_clock, acc = ck_it funs.global_funs acc vd.v_clock in
  { vd with v_type = v_type; v_clock = v_clock; v_ident = v }, acc

and var_decs_it funs acc vds = funs.var_decs funs acc vds
and var_decs funs acc vds = mapfold (var_dec_it funs) acc vds

and objective_it funs acc o = funs.objective funs acc o
and objective funs acc o =
  let e, acc = extvalue_it funs acc o.o_exp in
  { o with o_exp = e }, acc

and contract_it funs acc c = funs.contract funs acc c
and contract funs acc c =
  let c_assume, acc = extvalue_it funs acc c.c_assume in
  let c_assume_loc, acc = extvalue_it funs acc c.c_assume_loc in
  let c_objectives, acc = mapfold (objective_it funs) acc c.c_objectives in
  let c_enforce_loc, acc = extvalue_it funs acc c.c_enforce_loc in
  let c_local, acc = var_decs_it funs acc c.c_local in
  let c_eq, acc = eqs_it funs acc c.c_eq in
  { c with
      c_assume = c_assume;
      c_objectives = c_objectives;
      c_assume_loc = c_assume_loc;
      c_enforce_loc = c_enforce_loc;
      c_local = c_local;
      c_eq = c_eq }
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


and type_dec_it funs acc t =
  try funs.type_dec funs acc t
  with Fallback -> type_dec funs acc t
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
  objective = objective;
  contract = contract;
  node_dec = node_dec;
  const_dec = const_dec;
  type_dec = type_dec;
  tdesc = tdesc;
  program = program;
  program_desc = program_desc;
  global_funs = Global_mapfold.defaults }
