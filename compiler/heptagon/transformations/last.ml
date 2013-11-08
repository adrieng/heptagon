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
(* removing accessed to shared variables (last x)      *)
open Heptagon
open Hept_utils
open Hept_mapfold
open Idents


let fresh = Idents.gen_fresh "last" Idents.name


(* introduce a fresh equation [last_x = pre(x)] for every *)
(* variable declared with a last *)
let last (eq_list, env, v) { v_ident = n; v_type = t; v_linearity = lin; v_last = last } =
  match last with
    | Var -> (eq_list, env, v)
    | Last(default) ->
        let lastn = fresh n in
        let eq =
          mk_equation (Eeq (Evarpat lastn,
                            mk_exp (Epre (default,
                                          mk_exp (Evar n) t ~linearity:Linearity.Ltop))
                              t ~linearity:lin)) in
        eq:: eq_list,
        Env.add n lastn env,
        (mk_var_dec lastn t ~linearity:lin) :: v

let extend_env env v = List.fold_left last ([], env, []) v

let edesc _ env ed = match ed with
  | Elast x ->
      let lx = Env.find x env in Evar lx, env
  | _ -> raise Errors.Fallback

let block funs env b =
  let eq_lastn_n_list, env, last_v = extend_env env b.b_local in
  let b, _ = Hept_mapfold.block funs env b in
    { b with b_local = b.b_local @ last_v;
        b_equs = eq_lastn_n_list @ b.b_equs }, env

let node_dec funs _ n =
  Idents.enter_node n.n_name;
  let _, env, _ = extend_env Env.empty n.n_input in
  let eq_lasto_list, env, last_o = extend_env env n.n_output in
  let n, _  = Hept_mapfold.node_dec funs env n in
    { n with n_block =
        { n.n_block with b_local = n.n_block.b_local @ last_o;
            b_equs = eq_lasto_list @ n.n_block.b_equs } }, env

let program p =
  let funs = { Hept_mapfold.defaults with
                 node_dec = node_dec; block = block; edesc = edesc } in
  let p, _ = Hept_mapfold.program_it funs Env.empty p in
    p
