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


let check_implementation modul filename =
  (* input and output files *)
  let source_name = filename ^ ".ept" in

  let ic, lexbuf = lexbuf_from_file source_name in
  let close_all_files () =
    close_in ic
  in

  try
    Initial.initialize modul;
    add_include (Filename.dirname filename);

    (* Parsing of the file *)
    let p = do_silent_pass "Parsing" (parse_implementation modul) lexbuf in

    (* Fuse static exps together *)
    let p = do_silent_pass "Static Scoping"
      Hept_static_scoping.program p in
    (* Convert the parse tree to Heptagon AST *)
    let p = do_pass "Scoping" Hept_scoping.translate_program p pp in

    (* Call the compiler*)
    let _ = compile_impl pp p in

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
    | Errors.Error -> exit 2;;

main ()


