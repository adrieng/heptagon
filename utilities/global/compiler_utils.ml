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

let lexical_error err loc =
  Printf.eprintf "%aIllegal character.\n" output_location loc;
  raise Error

let syntax_error loc =
  Printf.eprintf "%aSyntax error.\n" output_location loc;
  raise Error

let language_error lang =
  Printf.eprintf "Unknown language: %s.\n" lang

let parse parsing_fun lexing_fun lexbuf =
  try
    parsing_fun lexing_fun lexbuf
  with
    | Lexer.Lexical_error(err, pos1, pos2) ->
        lexical_error err (Loc(pos1, pos2))
    | Parsing.Parse_error ->
        let pos1 = Lexing.lexeme_start lexbuf
        and pos2 = Lexing.lexeme_end lexbuf in
        let l = Loc(pos1,pos2) in
        syntax_error l

let comment s = Printf.printf "** %s done **\n" s; flush stdout

let do_pass f d p pp enabled =
  if enabled
  then
    let r = f p in
    if !verbose
    then begin
      comment d;
      pp r;
    end;
    r
  else p

let do_silent_pass f d p enabled =
  if enabled
  then begin
    let r = f p in
    if !verbose then comment d; r
  end
  else p
