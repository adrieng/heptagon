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

open Compiler_options
open Compiler_utils
open Location

let parse parsing_fun lexbuf =
  try
    parsing_fun Hept_lexer.token lexbuf
  with
    | Hept_lexer.Lexical_error(err, l) ->
        lexical_error err l
    | Hept_parser.Error ->
        let pos1 = Lexing.lexeme_start_p lexbuf
        and pos2 = Lexing.lexeme_end_p lexbuf in
        let l = Loc(pos1,pos2) in
        syntax_error l

(** Parse an implementation [lexbuf] *)
let parse_program modname lexbuf out_log =

  let pp p = if !verbose then Hept_printer.print out_log p in

  (* Parsing of the file *)
  let p = do_silent_pass "Parsing" (parse Hept_parser.program) lexbuf in
  let p = { p with Hept_parsetree.p_modname = modname } in


  (* Fuse static exps together *)
  let p = do_silent_pass "Static Scoping" Hept_static_scoping.program p in

  (* Convert the parse tree to Heptagon AST *)
  let p = do_pass "Scoping" Hept_scoping.translate_program p pp in
  p

(** Parse an interface [lexbuf] *)
let parse_interface modname lexbuf =
  (* Parsing of the file *)
  let i = do_silent_pass "Parsing" (parse Hept_parser.interface) lexbuf in
  let i = { i with Hept_parsetree.i_modname = modname } in

  (* Fuse static exps together *)
  let i = do_silent_pass "Static Scoping" Hept_static_scoping.interface i in

  (* Convert the parse tree to Heptagon AST *)
  let i = do_silent_pass "Scoping" Hept_scoping.translate_interface i in
  i
