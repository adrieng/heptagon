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

let init_compiler modname source_name ic =
    Location.initialize source_name ic;
    Modules.initialize modname;
    Initial.initialize ()

let pp = Printer.print stdout

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
        Hept_compiler.compile_impl pp p;

        if !verbose
        then begin
          comment "Check successfull"
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
      Hept_compiler.compile_interface l;

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

let doc_verbose = "\t\t\tSet verbose mode"
and doc_version = "\t\tThe version of the compiler"
and doc_print_types = "\t\t\tPrint types"
and doc_include = "<dir>\t\tAdd <dir> to the list of include directories"
and doc_stdlib = "<dir>\t\tDirectory for the standard library"
and doc_locate_stdlib = "\t\tLocate standard libray"
and doc_no_pervasives = "\tDo not load the pervasives module"
and doc_full_type_info = "\t\t\tPrint full type information"
and doc_noinit = "\t\tDisable initialization analysis"

let errmsg = "Options are:"

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


