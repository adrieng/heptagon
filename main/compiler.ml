(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* $Id$ *)

open Location
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
    Location.initialize source_name ic;
    Modules.initialize modname;
    Initial.initialize ();

    (* Parsing of the file *)
    let lexbuf = Lexing.from_channel ic in
    let l = parse_interface lexbuf in

    (* Convert the parse tree to Heptagon AST *)
    let l = Scoping.translate_interface l in

    Interface.Type.main l;
    Modules.write itc;
    if !print_types then Interface.Printer.print stdout;
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
    Hept_compiler.compile pp p;

    (* Compile Heptagon to MinilLs *)
    let p = Hep2mls.program p;

    let pp = Minils.Printer.print stdout in
    if !verbose then comment "Translation into MiniLs";
    Minils.Printer.print mlsc p;

    (* Process the MiniLs AST *)
    Mls_compiler.compile pp p;

    (* Compile MiniLs to Obc *)
    let o = Mls2obc.program p in
    if !verbose then comment "Translation into Obc";
    Obc.Printer.print obc o;

    let pp = Obc.Printer.print stdout in
      if !verbose then pp o;

    (* Translation into dataflow and sequential languages *)
    targets filename p o !target_languages;

    close_all_files ();

  with x -> close_all_files (); raise x
