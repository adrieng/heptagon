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
(* removing present statements *)

open Heptagon
open Hept_utils
open Hept_mapfold

let translate_present_handlers handlers cont =
  let translate_present_handler { p_cond = e; p_block = b } cont =
    let stateful = b.b_stateful || cont.b_stateful in
      mk_block ~stateful:stateful ~defnames:b.b_defnames
        [mk_switch_equation e
           [{ w_name = Initial.ptrue; w_block = b };
            { w_name = Initial.pfalse; w_block = cont }]] in
  let b = List.fold_right translate_present_handler handlers cont in
    (List.hd (b.b_equs)).eq_desc

let eqdesc funs acc eqd =
  let eqd, _ = Hept_mapfold.eqdesc funs acc eqd in
    match eqd with
      | Epresent(ph, b) -> translate_present_handlers ph b, acc
      | _ -> eqd, acc

let program p =
  let funs = { Hept_mapfold.defaults with eqdesc = eqdesc } in
  let p, _ = Hept_mapfold.program_it funs false p in
    p
