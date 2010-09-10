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
open Global_printer

let pp p = if !verbose then Hept_printer.print stdout p

let parse parsing_fun lexing_fun lexbuf =
  try
    parsing_fun lexing_fun lexbuf
  with
    | Hept_lexer.Lexical_error(err, l) ->
        lexical_error err l
    | Hept_parser.Error ->
        let pos1 = Lexing.lexeme_start_p lexbuf
        and pos2 = Lexing.lexeme_end_p lexbuf in
        let l = Loc(pos1,pos2) in
        syntax_error l

let parse_implementation modname lexbuf =
  let p = parse Hept_parser.program Hept_lexer.token lexbuf in
  { p with Hept_parsetree.p_modname = modname }

let parse_interface lexbuf =
  parse Hept_parser.interface Hept_lexer.token lexbuf


let compile_impl pp p =
  (* Typing *)
  (*let p = pass "Typing" true Typing.program p pp in*)
  let p = silent_pass "Statefullness check" true Statefull.program p in

  if !print_types then print_interface Format.std_formatter p;

  (* Causality check *)
  let p = silent_pass "Causality check" true Causality.program p in

  (* Initialization check *)(*
  let p = silent_pass "Initialization check" !init Initialization.program p in*)

  (* Completion of partial definitions *)
  let p = pass "Completion" true Completion.program p pp in

  (* Inlining *)(*
  let p =
    let call_inline_pass = (List.length !inline > 0) || !Misc.flatten in
    pass "Inlining" call_inline_pass Inline.program p pp in *)

  (* Automata *)
  (*let p = pass "Automata" true Automata.program p pp in*)

  (* Present *)
  let p = pass "Present" true Present.program p pp in

  (* Shared variables (last) *)
  let p = pass "Last" true Last.program p pp in

  (* Reset *)
  let p = pass "Reset" true Reset.program p pp in

  (* Every *)
  let p = pass "Every" true Every.program p pp in

  (* Return the transformed AST *)
  p

let compile_interface modname filename =
  (* input and output files *)
  let source_name = filename ^ ".epi" in
  let obj_interf_name = filename ^ ".epci" in

  let ic, lexbuf = lexbuf_from_file source_name in
  let itc = open_out_bin obj_interf_name in
  let close_all_files () =
    close_in ic;
    close_out itc in

  try
    init_compiler modname;

    (* Parsing of the file *)
    let l = do_silent_pass "Parsing" parse_interface lexbuf in

    (* Convert the parse tree to Heptagon AST *)
    let l = do_silent_pass "Scoping" Hept_scoping.translate_interface l in
    if !print_types then print_interface Format.std_formatter l;


      output_value itc (Modules.current_module ());

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
