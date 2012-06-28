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

open Clocks
open Minils

(* Any clock variable left after clocking is free and should be set to level_ck.
   Since inputs and outputs are grounded to Cbase, this happens when
   no data dependence exists between an expression and the inputs/outputs.*)

(* We are confident that it is sufficient to unify level_ck with base_ck
   for expressions having a base_ck == Cvar.
   The other ones are coming from one like this one,
   indeed if it was Con (Cvar,c,x) x would have to be defined with an expression of clock Cvar.*)

let eq _ acc eq =
  let _ = match ck_repr eq.eq_base_ck with
    | Cvar {contents = Cindex _} -> unify_ck eq.eq_base_ck eq.eq_rhs.e_level_ck
    | _ -> ()
  in
  eq,acc (* no recursion since in minils exps are not recursive *)

let program p =
  let funs = { Mls_mapfold.defaults with Mls_mapfold.eq = eq } in
  let p, _ = Mls_mapfold.program_it funs [] p in
  p
