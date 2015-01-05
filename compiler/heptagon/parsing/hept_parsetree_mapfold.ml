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
(* Generic mapred over Heptagon Parsetree AST *)

open Misc
open Errors
(*open Global_mapfold*)
open Hept_parsetree

type 'a hept_it_funs = {
  ty              : 'a hept_it_funs -> 'a -> ty -> ty * 'a;
  static_exp      : 'a hept_it_funs -> 'a -> static_exp -> static_exp * 'a;
  static_exp_desc : 'a hept_it_funs -> 'a -> static_exp_desc -> static_exp_desc * 'a;
  app             : 'a hept_it_funs -> 'a -> app -> app * 'a;
  block           : 'a hept_it_funs -> 'a -> block -> block * 'a;
  edesc           : 'a hept_it_funs -> 'a -> edesc -> edesc * 'a;
  eq              : 'a hept_it_funs -> 'a -> eq -> eq * 'a;
  eqdesc          : 'a hept_it_funs -> 'a -> eqdesc -> eqdesc * 'a;
  escape_unless   : 'a hept_it_funs -> 'a -> escape -> escape * 'a;
  escape_until    : 'a hept_it_funs -> 'a -> escape -> escape * 'a;
  exp             : 'a hept_it_funs -> 'a -> exp -> exp * 'a;
  pat             : 'a hept_it_funs -> 'a -> pat -> pat * 'a;
  present_handler : 'a hept_it_funs -> 'a -> present_handler -> present_handler * 'a;
  state_handler   : 'a hept_it_funs -> 'a -> state_handler -> state_handler * 'a;
  switch_handler  : 'a hept_it_funs -> 'a -> switch_handler -> switch_handler * 'a;
  var_dec         : 'a hept_it_funs -> 'a -> var_dec -> var_dec * 'a;
  arg             : 'a hept_it_funs -> 'a -> arg -> arg * 'a;
  last            : 'a hept_it_funs -> 'a -> last -> last * 'a;
  objective       : 'a hept_it_funs -> 'a -> objective -> objective * 'a;
  contract        : 'a hept_it_funs -> 'a -> contract -> contract * 'a;
  node_dec        : 'a hept_it_funs -> 'a -> node_dec -> node_dec * 'a;
  const_dec       : 'a hept_it_funs -> 'a -> const_dec -> const_dec * 'a;
  type_dec        : 'a hept_it_funs -> 'a -> type_dec -> type_dec * 'a;
  type_desc       : 'a hept_it_funs -> 'a -> type_desc -> type_desc * 'a;
  program         : 'a hept_it_funs -> 'a -> program -> program * 'a;
  program_desc    : 'a hept_it_funs -> 'a -> program_desc -> program_desc * 'a;
  interface       : 'a hept_it_funs -> 'a -> interface -> interface * 'a;
  interface_desc  : 'a hept_it_funs -> 'a -> interface_desc -> interface_desc * 'a;
  signature       : 'a hept_it_funs -> 'a -> signature -> signature * 'a; }

let rec static_exp_it funs acc se = funs.static_exp funs acc se
and static_exp funs acc se =
  let se_desc, acc = static_exp_desc_it funs acc se.se_desc in
  { se with se_desc = se_desc }, acc

and static_exp_desc_it funs acc sd =
  try funs.static_exp_desc funs acc sd
  with Fallback -> static_exp_desc funs acc sd

and static_exp_desc funs acc sd = match sd with
  | Svar _ | Sint _ | Sfloat _ | Sbool _ | Sstring _ | Sconstructor _ | Sfield _ -> sd, acc
  | Stuple se_l ->
      let se_l, acc = mapfold (static_exp_it funs) acc se_l in
      Stuple se_l, acc
  | Sarray se_l ->
      let se_l, acc = mapfold (static_exp_it funs) acc se_l in
      Sarray se_l, acc
  | Sop (n, se_l) ->
      let se_l, acc = mapfold (static_exp_it funs) acc se_l in
      Sop (n, se_l), acc
  | Sarray_power (se1, se_l) ->
      let se1, acc = static_exp_it funs acc se1 in
      let se_l, acc = mapfold (static_exp_it funs) acc se_l in
      Sarray_power(se1, se_l), acc
  | Srecord f_se_l ->
      let aux acc (f,se) = let se,acc = static_exp_it funs acc se in
        (f, se), acc in
      let f_se_l, acc = mapfold aux acc f_se_l in
      Srecord f_se_l, acc


and exp_it funs acc e = funs.exp funs acc e
and exp funs acc e =
  let e_desc, acc = edesc_it funs acc e.e_desc in
  { e with e_desc = e_desc }, acc

and edesc_it funs acc ed =
  try funs.edesc funs acc ed
  with Fallback -> edesc funs acc ed
and edesc funs acc ed = match ed with
  | Econst se ->
      let se, acc = static_exp_it funs acc se in
      Econst se, acc
  | Evar _ | Elast _ -> ed, acc
  | Epre (se, e) ->
      let se, acc = optional_wacc (exp_it funs) acc se in
      let e, acc = exp_it funs acc e in
      Epre (se, e), acc
  | Efby (e1, e2) ->
      let e1, acc = exp_it funs acc e1 in
      let e2, acc = exp_it funs acc e2 in
      Efby (e1,e2), acc
  | Estruct n_e_list ->
      let aux acc (n,e) =
        let e, acc = exp_it funs acc e in
        (n,e), acc in
      let n_e_list, acc = mapfold aux acc n_e_list in
      Estruct n_e_list, acc
  | Emerge (x, c_e_list) ->
    let aux acc (c,e) =
      let e, acc = exp_it funs acc e in
        (c,e), acc in
    let c_e_list, acc = mapfold aux acc c_e_list in
      Emerge(x, c_e_list), acc
  | Ewhen (e, c, x) ->
    let e, acc = exp_it funs acc e in
      Ewhen (e, c, x), acc
  | Esplit (x, e2) ->
      let e2, acc = exp_it funs acc e2 in
        Esplit(x, e2), acc
  | Eapp (app, args) ->
      let app, acc = app_it funs acc app in
      let args, acc = mapfold (exp_it funs) acc args in
      Eapp (app, args), acc
  | Eiterator (i, app, params, pargs, args) ->
      let app, acc = app_it funs acc app in
      let params, acc = mapfold (exp_it funs) acc params in
      let pargs, acc = mapfold (exp_it funs) acc pargs in
      let args, acc = mapfold (exp_it funs) acc args in
      Eiterator (i, app, params, pargs, args), acc


and app_it funs acc a = funs.app funs acc a
and app funs acc a =
  let p, acc = mapfold (exp_it funs) acc a.a_params in
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
  let eqdesc, acc = eqdesc_it funs acc eq.eq_desc in
  { eq with eq_desc = eqdesc }, acc


and eqdesc_it funs acc eqd =
  try funs.eqdesc funs acc eqd
  with Fallback -> eqdesc funs acc eqd
and eqdesc funs acc eqd = match eqd with
  | Eautomaton st_h_l ->
      let st_h_l, acc = mapfold (state_handler_it funs) acc st_h_l in
      Eautomaton st_h_l, acc
  | Eswitch (e, sw_h_l) ->
      let e, acc = exp_it funs acc e in
      let sw_h_l, acc = mapfold (switch_handler_it funs) acc sw_h_l in
      Eswitch (e, sw_h_l), acc
  | Epresent (p_h_l, b) ->
      let p_h_l, acc = mapfold (present_handler_it funs) acc p_h_l in
      let b, acc = block_it funs acc b in
      Epresent (p_h_l, b), acc
  | Ereset (b, e) ->
      let b, acc = block_it funs acc b in
      let e, acc = exp_it funs acc e in
      Ereset (b, e), acc
  | Eblock b ->
      let b, acc = block_it funs acc b in
      Eblock b, acc
  | Eeq (p, inits, e) ->
      let p, acc = pat_it funs acc p in
      let e, acc = exp_it funs acc e in
      Eeq (p, inits, e), acc


and block_it funs acc b = funs.block funs acc b
and block funs acc b =
  (* defnames ty ?? *)
  let b_local, acc = mapfold (var_dec_it funs) acc b.b_local in
  let b_equs, acc = mapfold (eq_it funs) acc b.b_equs in
  { b with b_local = b_local; b_equs = b_equs }, acc


and state_handler_it funs acc s = funs.state_handler funs acc s
and state_handler funs acc s =
  let s_unless, acc = mapfold (escape_unless_it funs) acc s.s_unless in
  let s_block, acc = block_it funs acc s.s_block in
  let s_until, acc = mapfold (escape_until_it funs) acc s.s_until in
  { s with s_block = s_block; s_until = s_until; s_unless = s_unless }, acc


(** escape is a generic function to deal with the automaton state escapes,
    still the iterator function record differentiate until and unless
    with escape_until_it and escape_unless_it *)
and escape_unless_it funs acc esc = funs.escape_unless funs acc esc
and escape_until_it funs acc esc = funs.escape_until funs acc esc
and escape funs acc esc =
  let e_cond, acc = exp_it funs acc esc.e_cond in
  { esc with e_cond = e_cond }, acc


and switch_handler_it funs acc sw = funs.switch_handler funs acc sw
and switch_handler funs acc sw =
  let w_block, acc = block_it funs acc sw.w_block in
  { sw with w_block = w_block }, acc


and present_handler_it funs acc ph = funs.present_handler funs acc ph
and present_handler funs acc ph =
  let p_cond, acc = exp_it funs acc ph.p_cond in
  let p_block, acc = block_it funs acc ph.p_block in
  { p_cond = p_cond; p_block = p_block }, acc

and var_dec_it funs acc vd = funs.var_dec funs acc vd
and var_dec funs acc vd =
  let v_type, acc = ty_it funs acc vd.v_type in
  let v_last, acc = last_it funs acc vd.v_last in
  { vd with v_last = v_last; v_type = v_type }, acc

and arg_it funs acc a = funs.arg funs acc a
and arg funs acc a =
  let a_type, acc = ty_it funs acc a.a_type in
  { a with a_type = a_type }, acc

and last_it funs acc l =
  try funs.last funs acc l
  with Fallback -> last funs acc l
and last funs acc l = match l with
  | Var -> l, acc
  | Last sto ->
      let sto, acc = optional_wacc (exp_it funs) acc sto in
      Last sto, acc

and objective_it funs acc o = funs.objective funs acc o
and objective funs acc o =
  let e, acc = exp_it funs acc o.o_exp in
  { o with o_exp = e }, acc

and contract_it funs acc c = funs.contract funs acc c
and contract funs acc c =
  let c_assume, acc = exp_it funs acc c.c_assume in
  let c_objectives, acc = mapfold (objective_it funs) acc c.c_objectives in
  let c_assume_loc, acc = exp_it funs acc c.c_assume_loc in
  let c_enforce_loc, acc = exp_it funs acc c.c_enforce_loc in
  let c_block, acc = block_it funs acc c.c_block in
  { c with
      c_assume = c_assume;
      c_objectives = c_objectives;
      c_assume_loc = c_assume_loc;
      c_enforce_loc = c_enforce_loc;
      c_block = c_block }
  , acc


and node_dec_it funs acc nd = funs.node_dec funs acc nd
and node_dec funs acc nd =
  let n_input, acc = mapfold (var_dec_it funs) acc nd.n_input in
  let n_output, acc = mapfold (var_dec_it funs) acc nd.n_output in
  let n_params, acc = mapfold (var_dec_it funs) acc nd.n_params in
  let n_contract, acc =  optional_wacc (contract_it funs) acc nd.n_contract in
  let n_constraints, acc = mapfold (exp_it funs) acc nd.n_constraints in
  let n_block, acc = block_it funs acc nd.n_block in
  { nd with
      n_input = n_input;
      n_output = n_output;
      n_block = n_block;
      n_params = n_params;
      n_constraints = n_constraints;
      n_contract = n_contract }
  , acc


and ty_it funs acc t = try funs.ty funs acc t with Fallback -> ty funs acc t
and ty funs acc t = match t with
  | Tid _ | Tinvalid -> t, acc
  | Tprod t_l -> let t_l, acc = mapfold (ty_it funs) acc t_l in Tprod t_l, acc
  | Tarray (t, e) ->
      let t, acc = ty_it funs acc t in
      let e, acc = exp_it funs acc e in
      Tarray (t, e), acc


and const_dec_it funs acc c = funs.const_dec funs acc c
and const_dec funs acc c =
  let c_type, acc = ty_it funs acc c.c_type in
  let c_value, acc = exp_it funs acc c.c_value in
  { c with c_value = c_value; c_type = c_type }, acc


and type_dec_it funs acc td = funs.type_dec funs acc td
and type_dec funs acc td =
  let t_desc, acc = type_desc_it funs acc td.t_desc in
  { td with t_desc = t_desc }, acc

and type_desc_it funs acc td =
  try funs.type_desc funs acc td with Fallback -> type_desc funs acc td
and type_desc funs acc td = match td with
  | Type_abs
  | Type_enum _ -> td, acc
  | Type_alias ty ->
      let ty, acc = ty_it funs acc ty in
        Type_alias ty, acc
  | Type_struct c_t_list ->
      let aux acc (f,ty) = let ty,acc = ty_it funs acc ty in
        (f, ty), acc in
      let c_t_list, acc = mapfold aux acc c_t_list in
        Type_struct c_t_list, acc

and program_it funs acc p = funs.program funs acc p
and program funs acc p =
  let p_desc, acc = mapfold (program_desc_it funs) acc p.p_desc in
  { p with p_desc = p_desc }, acc

and program_desc_it funs acc pd =
  try funs.program_desc funs acc pd
  with Fallback -> program_desc funs acc pd
and program_desc funs acc pd = match pd with
  | Pconst c -> let c, acc = const_dec_it funs acc c in Pconst c, acc
  | Ptype t -> let t, acc = type_dec_it funs acc t in Ptype t, acc
  | Pnode n -> let n, acc = node_dec_it funs acc n in Pnode n, acc
  | Ppragma _ -> pd, acc

and interface_desc_it funs acc id =
  try funs.interface_desc funs acc id
  with Fallback -> interface_desc funs acc id
and interface_desc funs acc id = match id with
  | Itypedef t -> let t, acc = type_dec_it funs acc t in Itypedef t, acc
  | Iconstdef c -> let c, acc = const_dec_it funs acc c in Iconstdef c, acc
  | Isignature s -> let s, acc = signature_it funs acc s in Isignature s, acc

and interface_it funs acc i = funs.interface funs acc i
and interface funs acc i =
  let desc, acc = mapfold (interface_desc_it funs) acc i.i_desc in
  { i with i_desc = desc }, acc

and signature_it funs acc s = funs.signature funs acc s
and signature funs acc s =
  let sig_inputs, acc = mapfold (arg_it funs) acc s.sig_inputs in
  let sig_outputs, acc = mapfold (arg_it funs) acc s.sig_outputs in
  let sig_params, acc = mapfold (var_dec_it funs) acc s.sig_params in
  let sig_param_constraints, acc = mapfold (exp_it funs) acc s.sig_param_constraints in
  { s with sig_inputs = sig_inputs;
           sig_outputs = sig_outputs;
           sig_params = sig_params;
           sig_param_constraints = sig_param_constraints; }
  , acc


let defaults = {
  ty = ty;
  static_exp = static_exp;
  static_exp_desc = static_exp_desc;
  app = app;
  block = block;
  edesc = edesc;
  eq = eq;
  eqdesc = eqdesc;
  escape_unless = escape;
  escape_until = escape;
  exp = exp;
  pat = pat;
  present_handler = present_handler;
  state_handler = state_handler;
  switch_handler = switch_handler;
  var_dec = var_dec;
  last = last;
  objective = objective;
  contract = contract;
  node_dec = node_dec;
  const_dec = const_dec;
  type_dec = type_dec;
  type_desc = type_desc;
  program = program;
  program_desc = program_desc;
  interface = interface;
  interface_desc = interface_desc;
  signature = signature;
  arg = arg; }



let defaults_stop = {
  ty = Global_mapfold.stop;
  static_exp = Global_mapfold.stop;
  static_exp_desc = Global_mapfold.stop;
  app = Global_mapfold.stop;
  block = Global_mapfold.stop;
  edesc = Global_mapfold.stop;
  eq = Global_mapfold.stop;
  eqdesc = Global_mapfold.stop;
  escape_unless = Global_mapfold.stop;
  escape_until = Global_mapfold.stop;
  exp = Global_mapfold.stop;
  pat = Global_mapfold.stop;
  present_handler = Global_mapfold.stop;
  state_handler = Global_mapfold.stop;
  switch_handler = Global_mapfold.stop;
  var_dec = Global_mapfold.stop;
  last = Global_mapfold.stop;
  objective = Global_mapfold.stop;
  contract = Global_mapfold.stop;
  node_dec = Global_mapfold.stop;
  const_dec = Global_mapfold.stop;
  type_dec = Global_mapfold.stop;
  type_desc = Global_mapfold.stop;
  program = Global_mapfold.stop;
  program_desc = Global_mapfold.stop;
  interface = Global_mapfold.stop;
  interface_desc = Global_mapfold.stop;
  signature = Global_mapfold.stop;
  arg = Global_mapfold.stop; }

