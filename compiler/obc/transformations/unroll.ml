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

(** Temporary hack to unroll for loops *)

open Obc
open Types
open Obc_utils
open Obc_mapfold


let fresh_for = fresh_for "scalarize"

let is_static e = match e.e_desc with
  | Eextvalue { w_desc = Wconst { se_desc = Sint i; }; } -> Some i
  | _ -> None

let unroll vd start stop b =
  let rec add c l =
    let ext_value funs () w = match w.w_desc with
      | Wvar vi ->
        (if Idents.ident_compare vi vd.v_ident = 0 then mk_ext_value_const_int c else w), ()
      | _ -> Obc_mapfold.extvalue funs () w
    in

    if c = stop
    then l
    else
      let funs = { Obc_mapfold.defaults with extvalue = ext_value; } in
      let new_b, () = Obc_mapfold.block funs () b in
      add (c + 1) (new_b.b_body :: l)
  in
  let l = add start [] in
  { b with b_body = List.concat (List.rev l); }

let act funs () a =
  let a, () = Obc_mapfold.act funs () a in
  match a with
    | Afor (vd, start, stop, b) ->
      (match is_static start, is_static stop with
        | Some z, Some n -> Ablock (unroll vd z n b), ()
        | _ -> a, ())
    | _ -> a, ()

let program p =
  let p, _ = program_it { defaults with act = act } () p in
  p
