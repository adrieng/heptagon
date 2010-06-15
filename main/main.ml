(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* the main *)

(* $Id$ *)

open Misc
open Compiler

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

let doc_verbose = "\t\t\tSet verbose mode"
and doc_version = "\t\tThe version of the compiler"
and doc_print_types = "\t\t\tPrint types"
and doc_include = "<dir>\t\tAdd <dir> to the list of include directories"
and doc_stdlib = "<dir>\t\tDirectory for the standard library"
and doc_sim = "<node>\t\tCreate simulation for node <node>"
and doc_locate_stdlib = "\t\tLocate standard libray"
and doc_no_pervasives = "\tDo not load the pervasives module"
and doc_target =
  "<lang>\tGenerate code in language <lang>\n\t\t\t(with <lang>=c, c-old,"
  ^ " vhdl_seq, vhdl_df,\n\t\t\t java, caml or z3z)"
and doc_full_type_info = "\t\t\tPrint full type information"
and doc_target_path =
  "<path>\tGenerated files will be placed in <path>\n\t\t\t(the directory is cleaned)"
and doc_boolean = "\t\tTranslate enumerated values towards boolean vectors"
and doc_deadcode = "\t\tDeadcode removal"
and doc_noinit = "\t\tDisable initialization analysis"
and doc_cse = "\t\t\tPerform common sub-expression elimination"
and doc_tomato = "\t\tPerform auTOMATa minimizatiOn"
and doc_sigali = "\t\t\tGenerate symbolic equations for Sigali (Z/3Z format)"
and doc_flatten = "<node name>\tRecursively inline all calls in specified node"
and doc_inline = "<node list>\tInline the list of nodes, separated by commas"
and doc_dep2dot = "<node list>\tOutput to .dot files the dependency graph of "
  ^ "the list of nodes, separated by commas"
and doc_intermediate = "\t\tPerform intermediate-equations removal (buggy)"
and doc_nomemalloc = "\t\tDisable memory allocation algorithm"
and doc_interfscheduler = "\tUse the new scheduler, that tries to minimise interference" 
and doc_main_node = "<node>\t\tUse <node> as the toplevel node"
and doc_new_reset = "\t\tUse the new alternate encoding of resets" 

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
        "-s", Arg.String set_simulation_node, doc_sim;
        "-nopervasives", Arg.Unit set_no_pervasives, doc_no_pervasives;
        "-target", Arg.String add_target_language, doc_target;
        "-targetpath", Arg.String set_target_path, doc_target_path;
        "-bool", Arg.Set boolean, doc_boolean;
        "-deadcode", Arg.Set deadcode, doc_deadcode;
	      "-noinit", Arg.Clear init, doc_noinit;
        "-fti", Arg.Set full_type_info, doc_full_type_info;
        "-cse", Arg.Set cse, doc_cse;
        "-tomato", Arg.Set tomato, doc_tomato;
        "-z3z", Arg.Unit set_sigali, doc_sigali;
        "-inter", Arg.Set intermediate, doc_intermediate;
        "-flatten", Arg.String (fun s -> node_to_flatten := Some s), doc_flatten;
        ("-inline",
         Arg.String (fun s -> nodes_to_inline := Misc.split_string s ','),
         doc_inline);
        ("-dep2dot",
         Arg.String (fun s -> nodes_to_display := Misc.split_string s ','),
         doc_dep2dot);
	"-nomemalloc", Arg.Set no_mem_alloc, doc_nomemalloc;
	"-interfscheduler", Arg.Set use_interf_scheduler, doc_interfscheduler;
	"-new-reset-encoding", Arg.Set use_new_reset_encoding, doc_new_reset;
      ]
      compile
      errmsg;
  with
    | Misc.Error -> exit 2;;

main ()
