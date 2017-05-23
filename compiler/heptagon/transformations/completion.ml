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
(* complete partial definitions with [x = last(x)] *)

open Heptagon
open Hept_utils
open Hept_mapfold
open Idents


(* We first define a shallow pass,
  meant to be called at an automaton/present/switch level
  It'll collect the set of defined names among the handlers of the automaton/...
*)

(* We stop at the first level, it'll correspond to an handler *)
let block_collect _ _ b =
  b, b.b_defnames

let gather f funs env x =
  let x, new_env = f funs Env.empty x in
  x, Env.union new_env env

(* We need to return the union of the defined names which is done with [gather],
  without traversing anything else.
  This funs_collect will stop directly if called on something else than
  blocks or handlers. *)
let funs_collect =
  { Hept_mapfold.defaults_stop with
      block = block_collect;
      switch_handler = gather Hept_mapfold.switch_handler;
      present_handler = gather Hept_mapfold.present_handler;
      state_handler = gather Hept_mapfold.state_handler; }



(* The real pass adding the needed equations *)

(* adds an equation [x = last(x)] for every partially defined variable *)
(* in a control structure *)
let complete_with_last defined_names local_defined_names eq_list =
  let last n vd = mk_exp (Elast n) vd.v_type ~linearity:Linearity.Ltop in
  let equation n vd eq_list =
    (mk_equation (Eeq(Evarpat n, last n vd)))::eq_list in
  let d = Env.diff defined_names local_defined_names in
  Env.fold equation d eq_list


let block funs defnames b =
  let b, _ = Hept_mapfold.block funs Env.empty b in (*recursive call*)
  let eqs = complete_with_last defnames b.b_defnames b.b_equs in
  { b with b_equs = eqs; b_defnames = defnames }
  , defnames

let eqdesc funs _ ed = match ed with
  | Epresent _ | Eautomaton _ | Eswitch _ ->
      (* collect defined names with the special pass *)
      let ed, defnames =
        Hept_mapfold.eqdesc funs_collect Env.empty ed in
      (* add missing defnames *)
      let ed, _defnames = Hept_mapfold.eqdesc funs defnames ed in
      ed, Env.empty
  | _ -> raise Errors.Fallback

let funs = { Hept_mapfold.defaults with eqdesc = eqdesc; block = block; }

let program p = let p, _ = program_it funs Env.empty p in p
