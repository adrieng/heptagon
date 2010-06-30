(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)


open Misc
open Compiler_utils
open Location

let pp p = if !verbose then Hept_printer.print stdout p

let parse parsing_fun lexing_fun lexbuf =
  try
    parsing_fun lexing_fun lexbuf
  with
    | Hept_lexer.Lexical_error(err, pos1, pos2) ->
        lexical_error err (Loc(pos1, pos2))
    | Hept_parser.Error ->
        let pos1 = Lexing.lexeme_start lexbuf
        and pos2 = Lexing.lexeme_end lexbuf in
        let l = Loc(pos1,pos2) in
        syntax_error l

let parse_implementation lexbuf =
  parse Hept_parser.program Hept_lexer.token lexbuf

let parse_interface lexbuf =
  parse Hept_parser.interface Hept_lexer.token lexbuf


let compile_impl pp p =
  (* Typing *)
  let p = do_pass Typing.program "Typing" p pp true in

  if !print_types then Interface.Printer.print stdout;

  (* Causality check *)
  let p = do_silent_pass Causality.program "Causality check" p true in

  (* Initialization check *)
  let p =
    do_silent_pass Initialization.program "Initialization check" p !init in

  (* Completion of partial definitions *)
  let p = do_pass Completion.program "Completion" p pp true in

  (* Automata *)
  let p = do_pass Automata.program "Automata" p pp true in

  (* Present *)
  let p = do_pass Present.program "Present" p pp true in

  (* Shared variables (last) *)
  let p = do_pass Last.program "Last" p pp true in

  (* Reset *)
  let p = do_pass Reset.program "Reset" p pp true in

  (* Every *)
  let p = do_pass Every.program "Every" p pp true in

  (* Return the transformed AST *)
  p

let compile_interface modname filename =
  (* input and output files *)
  let source_name = filename ^ ".epi" in
  let obj_interf_name = filename ^ ".epci" in

  let ic = open_in source_name in
  let itc = open_out_bin obj_interf_name in
  let close_all_files () =
    close_in ic;
    close_out itc in

  try
    init_compiler modname source_name ic;

    (* Parsing of the file *)
    let lexbuf = Lexing.from_channel ic in
    let l = parse_interface lexbuf in

    (* Convert the parse tree to Heptagon AST *)
    let l = Scoping.translate_interface l in

    (* Compile*)
    Interface.Type.main l;
    if !print_types then Interface.Printer.print stdout;


    Modules.write itc;

    close_all_files ()
  with
    | x -> close_all_files (); raise x


let compile compile_implementation file =
  if Filename.check_suffix file ".ept"
  then
    let filename = Filename.chop_suffix file ".ept" in
    let modname = String.capitalize(Filename.basename filename) in
    compile_implementation modname filename
  else if Filename.check_suffix file ".epi"
  then
    let filename = Filename.chop_suffix file ".epi" in
    let modname = String.capitalize(Filename.basename filename) in
    compile_interface modname filename
  else
    raise (Arg.Bad ("Unknow file type: " ^ file))
