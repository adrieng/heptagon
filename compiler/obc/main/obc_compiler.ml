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
open Compiler_utils
open Compiler_options

let compile_program out p =

  let pp p = if !verbose then Obc_printer.print out p in

  (* Memory allocation application *)
  let p = pass "Application of Memory Allocation"
    (!do_mem_alloc || !do_linear_typing) Memalloc_apply.program p pp in

  (*Scalarize for wanting backends*)
  let p = pass "Scalarize" (!do_scalarize) Scalarize.program p pp in

  (*Simplify*)
  let p = pass "Simplify" (!do_simplify) Simplify.program p pp in

  (*Dead code removal*)
  let p = pass "Dead code removal"
               (!do_mem_alloc || !do_linear_typing || !deadcode)
               Deadcode.program p pp in

  (*Control optimization*)
  let p = pass "Control optimization" true Control.program p pp in

  (*Loop unrolling*)
  let p = pass "Loop unrolling" !Compiler_options.unroll_loops Unroll.program p pp in

  p
