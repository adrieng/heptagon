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
open Hept_compiler
open Location


let check_implementation modname filename =
  (* input and output files *)
  let source_name = filename ^ ".ept" in

  let ic, lexbuf = lexbuf_from_file source_name in
  let close_all_files () =
    close_in ic
  in

  try
    init_compiler modname;

    (* Parsing of the file *)
    let p = parse_implementation lexbuf in

    (* Convert the parse tree to Heptagon AST *)
    let p = Hept_scoping.translate_program p in
    comment "Parsing";
    pp p;

    (* Call the compiler*)
    let p = Hept_compiler.compile_impl pp p in
    comment "Checking";

    close_all_files ()

  with x -> close_all_files (); raise x


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
      (compile check_implementation)
      errmsg;
  with
    | Misc.Error -> exit 2;;

main ()


