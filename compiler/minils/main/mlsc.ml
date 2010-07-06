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
open Mls2seq

let pp = Mls_printer.print stdout


let parse parsing_fun lexing_fun lexbuf =
  try
    parsing_fun lexing_fun lexbuf
  with
    | Mls_lexer.Lexical_error(err, pos1, pos2) ->
        lexical_error err (Loc(pos1, pos2))
    | Mls_parser.Error ->
        let pos1 = Lexing.lexeme_start lexbuf
        and pos2 = Lexing.lexeme_end lexbuf in
        let l = Loc(pos1,pos2) in
        syntax_error l


let parse_implementation lexbuf =
  parse Mls_parser.program Mls_lexer.token lexbuf

let compile_impl modname filename =
  (* input and output files *)
  (* input and output files *)
  let source_name = filename ^ ".mls"
  and mls_norm_name = filename ^ "_norm.mls"
  and obc_name = filename ^ ".obc" in

  let ic = open_in source_name
  and mlsnc = open_out mls_norm_name
  and obc = open_out obc_name in

  let close_all_files () =
    close_in ic;
    close_out obc;
    close_out mlsnc
  in

  try
    init_compiler modname source_name ic;

    (* Parsing of the file *)
    let lexbuf = Lexing.from_channel ic in
    let p = parse_implementation lexbuf in
    if !verbose
    then begin
      comment "Parsing";
      pp p
    end;

    (* Call the compiler*)
    let p = Mls_compiler.compile pp p in

    if !verbose
    then begin
      comment "Checking"
    end;

    (* Producing Object-based code *)
    let o = Mls2obc.program p in
    if !verbose then comment "Translation into Object-based code";
    Obc.Printer.print obc o;

    let pp = Obc.Printer.print stdout in
    if !verbose then pp o;

    (* Translation into dataflow and sequential languages *)
    targets filename p o !target_languages;

    close_all_files ()

  with x -> close_all_files (); raise x

let compile file =
  if Filename.check_suffix file ".mls" then
    let filename = Filename.chop_suffix file ".mls" in
    let modname = String.capitalize(Filename.basename filename) in
    compile_impl modname filename
  else
    raise (Arg.Bad ("Unknow file type: " ^ file))

let errmsg = "Options are:"

let main () =
  try
    Arg.parse
      [
        "-v", Arg.Set verbose, doc_verbose;
        "-assert", Arg.String add_assert, doc_assert;
        "-version", Arg.Unit show_version, doc_version;
        "-i", Arg.Set print_types, doc_print_types;
        "-I", Arg.String add_include, doc_include;
        "-where", Arg.Unit locate_stdlib, doc_locate_stdlib;
        "-stdlib", Arg.String set_stdlib, doc_stdlib;
        "-s", Arg.String set_simulation_node, doc_sim;
        "-nopervasives", Arg.Unit set_no_pervasives, doc_no_pervasives;
        "-target", Arg.String add_target_language, doc_target;
        "-targetpath", Arg.String set_target_path, doc_target_path;
        "-noinit", Arg.Clear init, doc_noinit;
        "-fti", Arg.Set full_type_info, doc_full_type_info;
      ]
      compile
      errmsg;
  with
    | Misc.Error -> exit 2;;

main ()
