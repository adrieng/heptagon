(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* the main *)

open Misc
open Compiler_utils

let parse_implementation lexbuf =
  parse Parser.program Lexer.token lexbuf

let parse_interface lexbuf =
  parse Parser.interface Lexer.token lexbuf

let interface modname filename =
  (* input and output files *)
  let source_name = filename ^ ".epi"
  and obj_interf_name = filename ^ ".epci" in

  let ic = open_in source_name
  and itc = open_out_bin obj_interf_name in
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

let compile modname filename =
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

    let pp = Printer.print stdout in

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

      (* Process the Heptagon AST *)
      let p = Hept_compiler.compile_impl pp p in

      (* Compile Heptagon to MiniLS *)
      let p = Hept2mls.program p in
        
      let pp = Minils_printer.print stdout in
        if !verbose then comment "Translation into MiniLs";
        Minils_printer.print mlsc p;
        
        (* Process the MiniLS AST *)
        let p = Mls_compiler.compile pp p in

          (* Compile MiniLS to Obc *)
          let o = Mls2obc.program p in
            (*if !verbose then*) comment "Translation into Obc";
            Obc.Printer.print obc o;
            
            let pp = Obc.Printer.print stdout in
              if !verbose then pp o;
              
              (* Translation into dataflow and sequential languages *)
              Mls2seq.targets filename p o !target_languages;
              
              close_all_files ()
                
  with 
    | x -> close_all_files (); raise x

let compile file =
  if Filename.check_suffix file ".ept"
  then
    let filename = Filename.chop_suffix file ".ept" in
    let modname = String.capitalize(Filename.basename filename) in
    compile modname filename
  else if Filename.check_suffix file ".epi"
  then
    let filename = Filename.chop_suffix file ".epi" in
    let modname = String.capitalize(Filename.basename filename) in
    interface modname filename
  else
    raise (Arg.Bad ("don't know what to do with " ^ file))

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
