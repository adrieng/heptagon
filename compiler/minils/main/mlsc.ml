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


let compile_impl modname filename =
  (* input and output files *)
  let source_name = filename ^ ".mls"
  and mls_norm_name = filename ^ "_norm.mls"
  and obc_name = filename ^ ".obc" in

  let ic, lexbuf = lexbuf_from_file source_name
  and mlsnc = open_out mls_norm_name
  and obc = open_out obc_name in

  let close_all_files () =
    close_in ic;
    close_out obc;
    close_out mlsnc
  in

  try
    init_compiler modname;

    (* Set pretty printer to the Minils one *)
    let pp = Mls_compiler.pp in

    (* Parsing of the file *)
    let p = do_silent_pass "Parsing" (Mls_compiler.parse_implementation modname)
                           lexbuf in

    (* Convert Parse tree to Minils AST *)
    let p = do_pass "Scoping" Mls_scoping.translate_program p pp in

    (* Process the MiniLS AST *)
    let p = Mls_compiler.compile pp p in

    (* Generate the sequential code *)
    Mls2seq.program p;

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
        "-version", Arg.Unit show_version, doc_version;
        "-i", Arg.Set print_types, doc_print_types;
        "-I", Arg.String add_include, doc_include;
        "-where", Arg.Unit locate_stdlib, doc_locate_stdlib;
        "-stdlib", Arg.String set_stdlib, doc_stdlib;
        "-c", Arg.Set create_object_file, doc_object_file;
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
