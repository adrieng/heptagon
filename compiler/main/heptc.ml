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
open Hept_compiler



let compile_impl modname filename =
  (* input and output files *)
  let source_name = filename ^ ".ept"
  and obj_interf_name = filename ^ ".epci"
  and mls_name = filename ^ ".mls"
  and obc_name = filename ^ ".obc"
  and ml_name = filename ^ ".ml" in

  let ic = open_in source_name
  and itc = open_out_bin obj_interf_name
  and mlsc = open_out mls_name
  and obc = open_out obc_name
  and mlc = open_out ml_name in

  let close_all_files () =
    close_in ic;
    close_out itc;
    close_out mlsc;
    close_out obc;
    close_out mlc in

  try
    init_compiler modname source_name ic;

    (* Parsing of the file *)
    let lexbuf = Lexing.from_channel ic in
    let p = parse_implementation lexbuf in

    (* Convert the parse tree to Heptagon AST *)
    let p = Scoping.translate_program p in
    comment "Parsing";

    pp p;

    (* Process the Heptagon AST *)
    let p = Hept_compiler.compile_impl pp p in
    Modules.write itc;

    (* Compile Heptagon to MiniLS *)
    let p = Hept2mls.program p in

    let pp = Mls_printer.print stdout in
    comment "Translation into MiniLs";
    Mls_printer.print mlsc p;

    (* Process the MiniLS AST *)
    let p = Mls_compiler.compile pp p in

    (* Compile MiniLS to Obc *)
    let o = Mls2obc.program p in
    comment "Translation into Obc";
    Obc.Printer.print obc o;

    let pp = Obc.Printer.print stdout in
    if !verbose then pp o;

    (* Translation into dataflow and sequential languages *)
    Mls2seq.targets filename p o !target_languages;

    close_all_files ()

  with
    | x -> close_all_files (); raise x



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
        "-s", Arg.String set_simulation_node, doc_sim;
        "-assert", Arg.String add_assert, doc_assert;
        "-nopervasives", Arg.Unit set_no_pervasives, doc_no_pervasives;
        "-target", Arg.String add_target_language, doc_target;
        "-targetpath", Arg.String set_target_path, doc_target_path;
        "-noinit", Arg.Clear init, doc_noinit;
        "-fti", Arg.Set full_type_info, doc_full_type_info;
      ]
      (compile compile_impl)
      errmsg;
  with
    | Misc.Error -> exit 2;;

main ()
