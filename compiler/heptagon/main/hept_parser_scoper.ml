(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Compiler_options
open Compiler_utils
open Location
open Global_printer

let pp p = if !verbose then Hept_printer.print stdout p

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
let parse_program modname lexbuf =
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
  (* TODO ?
  let i = { i with Hept_parsetree.=i_modname = modname } in *)

  (* Fuse static exps together *) (* TODO cf Hept_static_scoping *)
  (*let i = do_silent_pass "Static Scoping" Hept_static_scoping.interface i in *)

  (* Convert the parse tree to Heptagon AST *)
  let i = do_silent_pass "Scoping" Hept_scoping.translate_interface i in
  i

