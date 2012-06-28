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

(*
   Translate enumerated types (state variables) into boolean

   type t = A | B | C | D

   A --> 00
   B --> 01
   C --> 10
   D --> 11

   x : t --> x1,x2 : bool

   (e when A(x))
   -->
   (e when False(x1)) when False(x2)

   merge x (A -> e0) (B -> e1) (C -> e2) (D -> e3)
   -->
   merge x1 (False -> merge x2 (False -> e0) (True -> e1))
            (True  -> merge x2 (False -> e2) (True -> e3))
*)

(* $Id: boolean.mli 74 2009-03-11 10:21:25Z delaval $ *)

val program : Heptagon.program -> Heptagon.program
