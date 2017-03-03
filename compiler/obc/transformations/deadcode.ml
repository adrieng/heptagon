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
open Obc
open Obc_mapfold
open Types
open Initial

let act funs act_list a =
  let a, _ = Obc_mapfold.act funs [] a in
  match a with
  | Aassgn (lhs, e) -> (* remove x=x equations *)
     (match e.e_desc with
      | Eextvalue w when (Obc_compare.compare_lhs_extvalue lhs w = 0)
        -> a, act_list (* removal of action *)
      | _ -> a, a :: act_list
     )
  | Acase (_, []) -> a, act_list (* removal *)
  | Acase ({e_desc =
              Eextvalue(
                  {w_desc = Wconst ({se_desc = Sbool b})}
                )
           },
           c_b_l) ->
     let pb = if b then ptrue else pfalse in
     let c_b_l = List.filter (fun (c,_b) -> c = pb) c_b_l in
     begin
       match c_b_l with
         [_c,b] ->
         let a = Ablock b in
         a, a :: act_list
       | [] -> a, act_list
       | _ -> assert false (* More than one case after filter *)
     end
  | Acase ({e_desc =
              Eextvalue(
                  {w_desc = Wconst ({se_desc = Sconstructor ce})}
                )
           },
           c_b_l) ->
     let c_b_l = List.filter (fun (c,_b) -> c = ce) c_b_l in
     begin
       match c_b_l with
         [_c,b] ->
         let a = Ablock b in
         a, a :: act_list
       | [] -> a, act_list
       | _ -> assert false (* More than one case after filter *)
     end
  | Afor(_, _, _, { b_body = [] }) -> a, act_list (* removal *)
  | _ -> a, a :: act_list

let block funs acc b =
  let _, act_list = Obc_mapfold.block funs [] b in
    { b with b_body = List.rev act_list }, acc

let program p =
  let funs = { Obc_mapfold.defaults with block = block; act = act } in
  let p, _ = Obc_mapfold.program_it funs [] p in
    p

