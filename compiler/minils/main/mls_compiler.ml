(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
open Misc
open Location
open Compiler_utils

let pp p = if !verbose then Mls_printer.print stdout p

let parse parsing_fun lexing_fun lexbuf =
  try
    parsing_fun lexing_fun lexbuf
  with
    | Mls_lexer.Lexical_error(err, loc) ->
        lexical_error err loc
    | Mls_parser.Error ->
        let pos1 = Lexing.lexeme_start_p lexbuf
        and pos2 = Lexing.lexeme_end_p lexbuf in
        let l = Loc(pos1,pos2) in
        syntax_error l

let parse_implementation prog_name lexbuf =
  let p = parse Mls_parser.program Mls_lexer.token lexbuf in
  { p with Mls_parsetree.p_modname = prog_name }

let compile pp p =
  (* Clocking *)
  let p = pass "Clocking" true Clocking.program p pp in

  (* Check that the dataflow code is well initialized *)
  (*let p = silent_pass "Initialization check" !init Init.program p in *)

  (* Iterator fusion *)
  (*let p = pass "Iterator fusion" false Itfusion.program  p pp in*)

  (* Normalization to maximize opportunities *)
  let p = pass "Normalization" true Normalize.program p pp in

  (* Scheduling *)
  let p = pass "Scheduling" true Schedule.program p pp in

  p
