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

(** This module simplify static expression of the program and deal with :
    (0^n)[3] ==> 0
    [3,4,5][2] ==> 5
 *)



open Names
open Types
open Static
open Obc
open Obc_mapfold

let extvaluedesc funs acc evd = match evd with
  | Warray (ev,e) ->
      let ev, acc = extvalue_it funs acc ev in
      (match ev.w_desc with
        | Wconst se ->
          let se = simplify QualEnv.empty se in
          (match se.se_desc with
            | Sarray_power (sv, [_]) ->
              Wconst sv, acc
            | Sarray_power (sv, _::idx) ->
              Wconst { se with se_desc = Sarray_power (sv, idx)}, acc
            | Sarray sv_l ->
              (match e.e_desc with
                | Eextvalue { w_desc = Wconst i } ->
                  (try
                     let indice = int_of_static_exp QualEnv.empty i in
                     Wconst (Misc.nth_of_list (indice+1) sv_l), acc
                   with _ -> raise Errors.Fallback)
                | _ -> raise Errors.Fallback
              )
            | _ -> raise Errors.Fallback
          )
        | _ -> raise Errors.Fallback
      )
  | _ -> raise Errors.Fallback

let program p =
  let funs = { defaults with evdesc = extvaluedesc } in
  let p, _ = program_it funs [] p in
  p

