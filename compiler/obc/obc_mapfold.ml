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
(* Generic mapred over Obc Ast *)
open Misc
open Errors
open Global_mapfold
open Obc

type 'a obc_it_funs = {
  exp:          'a obc_it_funs -> 'a -> Obc.exp -> Obc.exp * 'a;
  edesc:        'a obc_it_funs -> 'a -> Obc.exp_desc -> Obc.exp_desc * 'a;
  lhs:          'a obc_it_funs -> 'a -> Obc.pattern -> Obc.pattern * 'a;
  lhsdesc:      'a obc_it_funs -> 'a -> Obc.pat_desc -> Obc.pat_desc * 'a;
  extvalue:     'a obc_it_funs -> 'a -> Obc.ext_value -> Obc.ext_value * 'a;
  evdesc:       'a obc_it_funs -> 'a -> Obc.ext_value_desc -> Obc.ext_value_desc * 'a;
  act:          'a obc_it_funs -> 'a -> Obc.act -> Obc.act * 'a;
  block:        'a obc_it_funs -> 'a -> Obc.block -> Obc.block * 'a;
  var_dec:      'a obc_it_funs -> 'a -> Obc.var_dec -> Obc.var_dec * 'a;
  var_decs:     'a obc_it_funs -> 'a -> Obc.var_dec list -> Obc.var_dec list * 'a;
  obj_dec:      'a obc_it_funs -> 'a -> Obc.obj_dec -> Obc.obj_dec * 'a;
  obj_decs:     'a obc_it_funs -> 'a -> Obc.obj_dec list -> Obc.obj_dec list * 'a;
  method_def:   'a obc_it_funs -> 'a -> Obc.method_def -> Obc.method_def * 'a;
  class_def:    'a obc_it_funs -> 'a -> Obc.class_def -> Obc.class_def * 'a;
  const_dec:    'a obc_it_funs -> 'a -> Obc.const_dec -> Obc.const_dec * 'a;
  type_dec:     'a obc_it_funs -> 'a -> Obc.type_dec -> Obc.type_dec * 'a;
  tdesc:        'a obc_it_funs -> 'a -> Obc.tdesc -> Obc.tdesc * 'a;
  program:      'a obc_it_funs -> 'a -> Obc.program -> Obc.program * 'a;
  program_desc: 'a obc_it_funs -> 'a -> Obc.program_desc -> Obc.program_desc * 'a;
  interface:    'a obc_it_funs -> 'a -> Obc.interface -> Obc.interface * 'a;
  interface_desc:    'a obc_it_funs -> 'a -> Obc.interface_desc -> Obc.interface_desc * 'a;
  signature:    'a obc_it_funs -> 'a -> Obc.signature -> Obc.signature * 'a;
  global_funs:  'a Global_mapfold.global_it_funs }


let rec exp_it funs acc e = funs.exp funs acc e
and exp funs acc e =
  let ed, acc = edesc_it funs acc e.e_desc in
  { e with e_desc = ed }, acc


and edesc_it funs acc ed =
  try funs.edesc funs acc ed
  with Fallback -> edesc funs acc ed
and edesc funs acc ed = match ed with
  | Eextvalue w ->
     let w, acc = extvalue_it funs acc w in
        Eextvalue w, acc
  | Eop (op, args) ->
       let args, acc = mapfold (exp_it funs) acc args in
         Eop (op, args), acc
  | Estruct(tyn, f_e_list) ->
      let aux acc (f,e) =
        let e, acc = exp_it funs acc e in
          (f,e), acc in
      let f_e_list, acc = mapfold aux acc f_e_list in
        Estruct(tyn, f_e_list), acc
  | Earray args ->
      let args, acc = mapfold (exp_it funs) acc args in
        Earray args, acc


and lhs_it funs acc l = funs.lhs funs acc l
and lhs funs acc l =
  let ld, acc = lhsdesc_it funs acc l.pat_desc in
  { l with pat_desc = ld }, acc


and lhsdesc_it funs acc ld =
  try funs.lhsdesc funs acc ld
  with Fallback -> lhsdesc funs acc ld
and lhsdesc funs acc ld = match ld with
  | Lvar x ->
      let x, acc = var_ident_it funs.global_funs acc x in
      Lvar x, acc
  | Lmem x ->
      let x, acc = var_ident_it funs.global_funs acc x in
      Lmem x, acc
  | Lfield(lhs, f) ->
      let lhs, acc = lhs_it funs acc lhs in
      Lfield(lhs, f), acc
  | Larray(lhs, e) ->
      let lhs, acc = lhs_it funs acc lhs in
      let e, acc = exp_it funs acc e in
      Larray(lhs, e), acc

and extvalue_it funs acc w = funs.extvalue funs acc w
and extvalue funs acc w =
  let wd, acc = evdesc_it funs acc w.w_desc in
  { w with w_desc = wd; }, acc

and evdesc_it funs acc wd =
  try funs.evdesc funs acc wd
  with Fallback -> evdesc funs acc wd
and evdesc funs acc wd = match wd with
  | Wvar x ->
      let x, acc = var_ident_it funs.global_funs acc x in
      Wvar x, acc
  | Wconst c ->
    let c, acc = static_exp_it funs.global_funs acc c in
    Wconst c, acc
  | Wmem x ->
      let x, acc = var_ident_it funs.global_funs acc x in
      Wmem x, acc
  | Wfield(w, f) ->
      let w, acc = extvalue_it funs acc w in
      Wfield(w, f), acc
  | Warray(w, e) ->
      let w, acc = extvalue_it funs acc w in
      let e, acc = exp_it funs acc e in
      Warray(w, e), acc

and act_it funs acc a =
  try funs.act funs acc a
  with Fallback -> act funs acc a
and act funs acc a = match a with
  | Aassgn(lhs, e) ->
      let lhs, acc = lhs_it funs acc lhs in
      let e, acc = exp_it funs acc e in
        Aassgn(lhs, e), acc
  | Aop(op_name, args) ->
      let args, acc = mapfold (exp_it funs) acc args in
        Aop(op_name, args), acc
  | Acall(lhs_list, obj, n, args) ->
      let lhs_list, acc = mapfold (lhs_it funs) acc lhs_list in
      let args, acc = mapfold (exp_it funs) acc args in
        Acall(lhs_list, obj, n, args), acc
  | Acase(e, c_b_list) ->
      let aux acc (c,b) =
        let b, acc = block_it funs acc b in
          (c,b), acc in
      let e, acc = exp_it funs acc e in
      let c_b_list, acc = mapfold aux acc c_b_list in
        Acase(e, c_b_list), acc
  | Afor(x, idx1, idx2, b) ->
      let idx1, acc = exp_it funs acc idx1 in
      let idx2, acc = exp_it funs acc idx2 in
      let b, acc = block_it funs acc b in
        Afor(x, idx1, idx2, b), acc
  | Ablock b ->
      let b, acc = block_it funs acc b in
      Ablock b, acc

and block_it funs acc b = funs.block funs acc b
and block funs acc b =
  let b_locals, acc = var_decs_it funs acc b.b_locals in
  let b_body, acc = mapfold (act_it funs) acc b.b_body in
  { b_locals = b_locals; b_body = b_body }, acc

and var_dec_it funs acc vd = funs.var_dec funs acc vd
and var_dec funs acc vd =
  let v_type, acc = ty_it funs.global_funs acc vd.v_type in
  let v, acc = var_ident_it funs.global_funs acc vd.v_ident in
  { vd with v_type = v_type; v_ident = v }, acc

and var_decs_it funs acc vds = funs.var_decs funs acc vds
and var_decs funs acc vds = mapfold (var_dec_it funs) acc vds


and obj_dec_it funs acc od = funs.obj_dec funs acc od
and obj_dec funs acc od =
  let o_size, acc = optional_wacc
    (mapfold (static_exp_it funs.global_funs)) acc od.o_size in
  let v, acc = var_ident_it funs.global_funs acc od.o_ident in
  { od with o_size = o_size; o_ident = v }, acc

and obj_decs_it funs acc ods = funs.obj_decs funs acc ods
and obj_decs funs acc ods = mapfold (obj_dec_it funs) acc ods


and method_def_it funs acc md = funs.method_def funs acc md
and method_def funs acc md =
  let m_inputs, acc = var_decs_it funs acc md.m_inputs in
  let m_outputs, acc = var_decs_it funs acc md.m_outputs in
  let m_body, acc = block_it funs acc md.m_body in
  { md with
      m_inputs = m_inputs; m_outputs = m_outputs; m_body = m_body }
  , acc


and class_def_it funs acc cd =
    Idents.enter_node cd.cd_name;
    funs.class_def funs acc cd
and class_def funs acc cd =
  let cd_mems, acc = var_decs_it funs acc cd.cd_mems in
  let cd_objs, acc = obj_decs_it funs acc cd.cd_objs in
  let cd_params, acc = mapfold (param_it funs.global_funs) acc cd.cd_params in
  let cd_methods, acc = mapfold (method_def_it funs) acc cd.cd_methods in
  { cd with
      cd_mems = cd_mems; cd_objs = cd_objs;
      cd_params = cd_params; cd_methods = cd_methods }
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
  | _ -> td, acc


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
  | Pclass n -> let n, acc = class_def_it funs acc n in Pclass n, acc


and interface_it funs acc p = funs.interface funs acc p
and interface funs acc p =
  let i_desc, acc = mapfold (interface_desc_it funs) acc p.i_desc in
  { p with i_desc = i_desc }, acc


and interface_desc_it funs acc pd =
  try funs.interface_desc funs acc pd
  with Fallback -> interface_desc funs acc pd
and interface_desc funs acc pd = match pd with
  | Itypedef td -> let td, acc = type_dec_it funs acc td in Itypedef td, acc
  | Iconstdef cd -> let cd, acc = const_dec_it funs acc cd in Iconstdef cd, acc
  | Isignature s -> let s, acc = signature_it funs acc s in Isignature s, acc


and signature_it funs acc s = funs.signature funs acc s
and signature funs acc s =
  let sig_params, acc = mapfold (param_it funs.global_funs) acc s.sig_params in
  let sig_inputs, acc = mapfold (arg_it funs.global_funs) acc s.sig_inputs in
  let sig_outputs, acc = mapfold (arg_it funs.global_funs) acc s.sig_outputs in
  { s with sig_params = sig_params; sig_inputs = sig_inputs; sig_outputs = sig_outputs }, acc


let defaults = {
  lhs = lhs;
  lhsdesc = lhsdesc;
  extvalue = extvalue;
  evdesc = evdesc;
  exp = exp;
  edesc = edesc;
  act = act;
  block = block;
  var_dec = var_dec;
  var_decs = var_decs;
  obj_dec = obj_dec;
  obj_decs = obj_decs;
  method_def = method_def;
  class_def = class_def;
  const_dec = const_dec;
  type_dec = type_dec;
  tdesc = tdesc;
  program = program;
  program_desc = program_desc;
  interface = interface;
  interface_desc = interface_desc;
  signature = signature;
  global_funs = Global_mapfold.defaults }
