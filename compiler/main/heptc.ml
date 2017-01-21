(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)


open Compiler_utils
open Compiler_options


let compile_interface modname source_f =

  (* output file names *)
  let output = String.uncapitalize_ascii modname in
  let epci_f = output ^ ".epci" in

  (* input/output channels *)
  let source_c, lexbuf = lexbuf_from_file source_f in
  let epci_c = open_out_bin epci_f in
  let close_all_files () = close_in source_c; close_out epci_c in

  try
  (* Process the [lexbuf] to an Heptagon AST *)
    let p = Hept_parser_scoper.parse_interface modname lexbuf in
    if !print_types then Global_printer.print_interface Format.std_formatter;

    (* Process the interface *)
    let p = Hept_compiler.compile_interface p in
    (* Output the .epci *)
    output_value epci_c (Modules.current_module ());
    (* Translate to Obc *)
    let p = Hept2mls.interface p in
    (* Generate the sequential code *)
    Mls2seq.interface p;
    close_all_files ()
  with
    | x -> close_all_files (); raise x

(* [modname] is the module name, [source_f] is the source file *)
let compile_program modname source_f =

  (* output file names *)
  let output = String.uncapitalize_ascii modname in
  let epci_f = output ^ ".epci" in
  let mls_f = output ^ ".mls" in
  let log_f = output ^ ".log" in

  (* input/output channels *)
  let source_c, lexbuf = lexbuf_from_file source_f in
  let epci_c = open_out_bin epci_f in
  let mls_c = open_out mls_f in
  let log_c = open_out log_f in
  let close_all_files () =
    close_in source_c;
    close_out epci_c;
    close_out mls_c;
    close_out log_c
  in

  try
  (* Activates passes according to the backend used *)
    Mls2seq.load_conf ();
  (* Record timing information *)
    Compiler_timings.start_compiling modname;
  (* Process the [lexbuf] to an Heptagon AST *)
    let p = Hept_parser_scoper.parse_program modname lexbuf log_c in
  (* Process the Heptagon AST *)
    let p = Hept_compiler.compile_program p log_c in
  (* Compile Heptagon to MiniLS *)
    let p = do_pass "Translation into MiniLS"
                    Hept2mls.program p (Mls_compiler.pp log_c) in
  (* Output the .mls *)
    do_silent_pass "MiniLS serialization" (fun () -> Mls_printer.print mls_c p) ();
  (* Process the MiniLS AST *)
    let p = Mls_compiler.compile_program p log_c in
  (* Output the .epci *)
    output_value epci_c (Modules.current_module ());
  (* Generate the sequential code *)
    Mls2seq.program p log_c;
    close_all_files ();
    Compiler_timings.report_statistics ()
  with x -> close_all_files (); raise x



let compile source_f =
  let modname = source_f
                |> Filename.basename
                |> Filename.chop_extension
                |> String.capitalize_ascii in
  let modul = Names.modul_of_string modname in
  Initial.initialize modul;
  source_f |> Filename.dirname |> add_include;
  check_options ();
  match Misc.file_extension source_f with
    | "ept" | "lus" -> compile_program modname source_f
    | "epi" -> compile_interface modname source_f
    | ext -> raise (Arg.Bad ("Unknow file type: " ^ ext ^ " for file: " ^ source_f))



(** [main] function to be launched *)
let main () =
  let read_qualname f =
    Arg.String (fun s -> f (try Names.qualname_of_string s with
      | Exit -> raise (Arg.Bad ("Invalid name: "^ s)))) in
  try
    Arg.parse
      [
        "-v",Arg.Set verbose, doc_verbose;
        "-version", Arg.Unit show_version, doc_version;
        "-i", Arg.Set print_types, doc_print_types;
        "-I", Arg.String add_include, doc_include;
        "-where", Arg.Unit locate_stdlib, doc_locate_stdlib;
        "-stdlib", Arg.String set_stdlib, doc_stdlib;
        "-c", Arg.Set create_object_file, doc_object_file;
        "-s", Arg.String set_simulation_node, doc_sim;
        "-hepts", Arg.Set hepts_simulation, doc_hepts;
        "-bool", Arg.Set boolean, doc_boolean;
        "-deadcode", Arg.Set deadcode, doc_deadcode;
        "-tomato", Arg.Set tomato, doc_tomato;
        "-tomanode", read_qualname add_tomato_node, doc_tomato;
        "-tomacheck", read_qualname add_tomato_check, "";
        "-inline", read_qualname add_inlined_node, doc_inline;
        "-flatten", Arg.Set flatten, doc_flatten;
        "-assert", Arg.String add_assert, doc_assert;
        "-nopervasives", Arg.Unit set_no_pervasives, doc_no_pervasives;
        "-target", Arg.String add_target_language, doc_target;
        "-targetpath", Arg.String set_target_path, doc_target_path;
        "-nocaus", Arg.Clear causality, doc_nocaus;
        "-noinit", Arg.Clear init, doc_noinit;
        "-fti", Arg.Set full_type_info, doc_full_type_info;
        "-statefuli", Arg.Set stateful_info, doc_stateful_info;
        "-fname", Arg.Set full_name, doc_full_name;
        "-nbvars", Arg.Set nbvars, doc_nbvars;
        "-itfusion", Arg.Set do_iterator_fusion, doc_itfusion;
        "-strict_ssa", Arg.Unit set_strict_ssa, doc_strict_ssa;
        "-nosink", Arg.Set nosink, doc_nosink;
        "-memalloc", Arg.Unit do_mem_alloc_and_typing, doc_memalloc;
        "-only-memalloc", Arg.Set do_mem_alloc, doc_memalloc_only;
        "-only-linear", Arg.Set do_linear_typing, doc_linear_only;
        "-old-scheduler", Arg.Set use_old_scheduler, doc_interf_scheduler;
        "-simple-scheduler", Arg.Set use_simple_scheduler, doc_simple_scheduler;
        "-unroll", Arg.Set unroll_loops, doc_unroll;
        "-O", Arg.Unit do_optim, doc_optim;
        "-mall", Arg.Set interf_all, doc_interf_all;
        "-time", Arg.Set time_passes, doc_time_passes;
        "-abstract-infinite", Arg.Set abstract_infinite, doc_abstract_infinite;
        ("-Wno-untranslatable", Arg.Clear warn_untranslatable,
         doc_no_warn_untranslat);
        ("-Wno-abstract", Arg.Clear warn_abstractions,
         doc_no_warn_abstractions);
      ]
        compile errmsg;
  with
    | Errors.Error -> exit 2;;


(* Launch the [main] *)
main ()
