(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* Checks the validity of a Heptagon file (interface or implementation).*)

open Misc
open Compiler_utils
open Location

let pp = Hept_printer.print stdout

let parse_implementation lexbuf =
  parse Parser.program Lexer.token lexbuf

let parse_interface lexbuf =
  parse Parser.interface Lexer.token lexbuf

let compile_impl modname filename =
  (* input and output files *)
  let source_name = filename ^ ".ept" in

  let ic = open_in source_name in
  let close_all_files () =
    close_in ic
  in

  try
    init_compiler modname source_name ic;

    (* Parsing of the file *)
    let lexbuf = Lexing.from_channel ic in
    let p = parse_implementation lexbuf in

    (* Convert the parse tree to Heptagon AST *)
    let p = Scoping.translate_program p in
    if !verbose
    then begin
      comment "Parsing";
      pp p
    end;

    (* Call the compiler*)
    let p = Hept_compiler.compile_impl pp p in

    if !verbose
    then begin
      comment "Checking"
    end;
    close_all_files ()

  with x -> close_all_files (); raise x

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

    (* Call the compiler*)
    let l = Hept_compiler.compile_interface l in

    Modules.write itc;

    close_all_files ()
  with
    | x -> close_all_files (); raise x

let compile file =
  if Filename.check_suffix file ".ept"
  then
    let filename = Filename.chop_suffix file ".ept" in
    let modname = String.capitalize(Filename.basename filename) in
    compile_impl modname filename
  else if Filename.check_suffix file ".epi"
  then
    let filename = Filename.chop_suffix file ".epi" in
    let modname = String.capitalize(Filename.basename filename) in
    compile_interface modname filename
  else
    raise (Arg.Bad ("Unknow file type: " ^ file))

let main () =
  try
    Arg.parse
      [
        "-v",Arg.Set verbose, doc_verbose;
        "-version", Arg.Unit show_version, doc_version;
        "-i", Arg.Set print_types, doc_print_types;
        "-I", Arg.String add_include, doc_include;
        "-where", Arg.Unit locate_stdlib, doc_locate_stdlib;
        "-stdlib", Arg.String set_stdlib, doc_stdlib;
        "-nopervasives", Arg.Unit set_no_pervasives, doc_no_pervasives;
        "-noinit", Arg.Clear init, doc_noinit;
        "-fti", Arg.Set full_type_info, doc_full_type_info;
      ]
      compile
      errmsg;
  with
    | Misc.Error -> exit 2;;

main ()


