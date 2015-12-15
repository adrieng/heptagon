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

exception Bad_format

type token = Modifier of string | Literal of string
type format = token list

let tail s start =
  String.sub s start (String.length s - start)

(** Return a list of expected types from a format string *)
let rec format_of_string s =
  try
    let i = String.index s '%' in
    let l = format_of_string (tail s (i+2)) in
    if i = 0 then
      let modifier = String.sub s 1 1 in
      (Modifier modifier)::l
    else
      let lit = String.sub s 0 i in
      let modifier = String.sub s (i+1) 1 in
      (Literal lit)::(Modifier modifier)::l
  with
    | Invalid_argument _ -> raise Bad_format (* String.get failed*)
    | Not_found -> [Literal s]

let types_of_format_string s =
  let ty_of_format f acc = match f with
    | Modifier "b" -> Initial.tbool::acc
    | Modifier "d" -> Initial.tint::acc
    | Modifier "f" -> Initial.tfloat::acc
    | Modifier "s" -> Initial.tstring::acc
    | _ -> acc
  in
  let sl = format_of_string s in
  List.fold_right ty_of_format sl []

let tr_format f s =
  let aux tok acc = match tok with
    | Literal s -> s^acc
    | Modifier m -> "%"^(f m)^acc
  in
  let sl = format_of_string s in
  List.fold_right aux sl ""
