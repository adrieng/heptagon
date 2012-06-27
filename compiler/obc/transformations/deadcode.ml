(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
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
open Obc
open Obc_mapfold

let is_deadcode = function
    | Aassgn (lhs, e) -> (* remove x=x equations *)
        (match e.e_desc with
           | Eextvalue w -> Obc_compare.compare_lhs_extvalue lhs w = 0
           | _ -> false
        )
    | Acase (_, []) -> true
    | Afor(_, _, _, { b_body = [] }) -> true
    | _ -> false

let act funs act_list a =
  let a, _ = Obc_mapfold.act funs [] a in
    if is_deadcode a then
      a, act_list
    else
      a, a::act_list

let block funs acc b =
  let _, act_list = Obc_mapfold.block funs [] b in
    { b with b_body = List.rev act_list }, acc

let program p =
  let funs = { Obc_mapfold.defaults with block = block; act = act } in
  let p, _ = Obc_mapfold.program_it funs [] p in
    p

