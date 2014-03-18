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
(* Checks that a node not declared unsafe is safe, and set app unsafe flag. *)
open Location
open Signature
open Modules
open Heptagon
open Hept_mapfold

type error =
  | Eshould_be_unsafe

let message loc kind =
  begin match kind with
    | Eshould_be_unsafe ->
        Format.eprintf "%aThis exp is unsafe but the current node is not declared unsafe.@."
          print_location loc
  end;
  raise Errors.Error

(* Returns whether an op is unsafe *)
let unsafe_op op = match op with
  | Enode f | Efun f ->
      (find_value f).node_unsafe
  | _ -> (*TODO il y a des op unsafe ??*)
      false

(* Update app unsafe field
   and gives an error if some exp is unsafe in a safe node ([unsafe]=false) *)
let exp funs unsafe e =
  let e, unsafe = Hept_mapfold.exp funs unsafe e in
    match e.e_desc with
      | Eapp({ a_op = op } as app, e_l, r) ->
          let u = (unsafe_op op) || app.a_unsafe in
          if u && (not unsafe)
          then message e.e_loc Eshould_be_unsafe
          else {e with e_desc = Eapp({ app with a_unsafe = u }, e_l, r)}, (unsafe || u)
      | Eiterator(it, ({ a_op = op } as app), n, pe_list, e_list, r) ->
          let u = (unsafe_op op) || app.a_unsafe in
          if u && (not unsafe)
          then message e.e_loc Eshould_be_unsafe
          else
            {e with e_desc = Eiterator(it, { app with a_unsafe = u }, n, pe_list, e_list, r)}
            , (unsafe || u)
      | _ -> e, unsafe

(* unsafe nodes are rejected if they are not declared unsafe *)
let node_dec funs _ n = Hept_mapfold.node_dec funs n.n_unsafe n

let funs =
  { Hept_mapfold.defaults with
      exp = exp;
      node_dec = node_dec; }

let program p =
  let p, _ = Hept_mapfold.program_it funs false p in
  p
