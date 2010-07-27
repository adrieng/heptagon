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

let parse_implementation lexbuf =
  parse Mls_parser.program Mls_lexer.token lexbuf

let compile pp p =
  (* Clocking *)
  let p = do_pass Clocking.program "Clocking" p pp true in

  (* Check that the dataflow code is well initialized *)
  (*let p = do_silent_pass Init.program "Initialization check" p !init in *)

  (* Iterator fusion *)
  let p = do_pass Itfusion.program "Iterator fusion" p pp true in

  (* Normalization to maximize opportunities *)
  let p = do_pass Normalize.program "Normalization" p pp true in

  (* Scheduling *)
  let p = do_pass Schedule.program "Scheduling" p pp true in

  p
