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
open Global

let lexical_error err loc =
  Printf.eprintf "%aIllegal character.\n" output_location loc;
  raise Error

let syntax_error loc =
  Printf.eprintf "%aSyntax error.\n" output_location loc;
  raise Error

let language_error lang =
  Printf.eprintf "Unknown language: %s.\n" lang

let parse parsing_fun lexing_fun lexbuf =
  try
    parsing_fun lexing_fun lexbuf
  with
    | Lexer.Lexical_error(err, pos1, pos2) ->
        lexical_error err (Loc(pos1, pos2))
    | Parsing.Parse_error ->
        let pos1 = Lexing.lexeme_start lexbuf
        and pos2 = Lexing.lexeme_end lexbuf in
        let l = Loc(pos1,pos2) in
        syntax_error l

let comment s = Printf.printf "** %s done **\n" s; flush stdout

let build_path suf =
  match !target_path with
    | None -> suf
    | Some path -> Filename.concat path suf

let clean_dir dir =
  if Sys.file_exists dir && Sys.is_directory dir
  then begin
    let rm_file_in_dir fn = Sys.remove (Filename.concat dir fn) in
    Array.iter rm_file_in_dir (Sys.readdir dir);
  end else Unix.mkdir dir 0o740;
  dir

(** Generation of a dataflow target *)
let dataflow_target filename p target_languages =
  let rec one_target = function
 (*   | "z3z" :: others ->
        let dirname = build_path (filename ^ "_z3z") in
        let dir = clean_dir dirname in
        let p = Dynamic_system.program p in
        if !verbose then
          comment "Translation into dynamic system (Z/3Z equations)";
        Sigali.Printer.print dir p;
        one_target others *)
    | ("vhdl_df" | "vhdl") :: others ->
        let dirname = build_path (filename ^ "_vhdl") in
        let dir = clean_dir dirname in
        let vhdl = Mls2vhdl.translate (Filename.basename filename) p in
        Vhdl.print dir vhdl;
        one_target others
    | unknown_lg :: others -> unknown_lg :: one_target others
    | [] -> [] in
  one_target target_languages

(** Generation of a sequential target *)
let sequential_target filename o target_languages =
  let rec one_target = function
    | "c-old" :: others ->
        let dirname = build_path (filename ^ "_c-old") in
        let dir = clean_dir dirname in
        C_old.print o dir;
          one_target others 
    | "java" :: others ->
        let dirname = build_path filename in
        let dir = clean_dir dirname in
        Java.print dir o;
        one_target others
    | "c" :: others ->
        let dirname = build_path (filename ^ "_c") in
        let dir = clean_dir dirname in
        let c_ast = Cgen.translate filename o in
        C.output dir c_ast;
        one_target others
    | "caml" :: others -> Caml.print filename o; one_target others
    | unknown_lg :: others -> unknown_lg :: one_target others
    | [] -> [] in
  one_target target_languages

(** Whole translation. *)
let targets filename df obc target_languages =
  let target_languages = dataflow_target filename df target_languages in
  let target_languages = sequential_target filename obc target_languages in
  match target_languages with
    | [] -> ()
    | target :: _ -> language_error target

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

let do_pass f d p pp enabled =
  if enabled
  then
    let r = f p in
    if !verbose
    then begin
      comment d;
      pp r;
    end;
    r
  else p

let do_silent_pass f d p enabled =
  if enabled
  then begin
    let r = f p in
    if !verbose then comment d; r
  end
  else p

let compile modname filename =
  (* input and output files *)
  let source_name = filename ^ ".ept"
  and obj_interf_name = filename ^ ".epci"
  and mls_name = filename ^ ".mls"
  and mls_norm_name = filename ^ "_norm.mls"
  and obc_name = filename ^ ".obc"
  and ml_name = filename ^ ".ml" in

  let ic = open_in source_name
  and itc = open_out_bin obj_interf_name
  and mlsc = open_out mls_name
  and mlsnc = open_out mls_norm_name
  and obc = open_out obc_name
  and mlc = open_out ml_name in

  let close_all_files () =
    close_in ic;
    close_out itc;
    close_out mlsc;
    close_out obc;
    close_out mlc in

  try
    Location.initialize source_name ic;
    Modules.initialize modname;
    Initial.initialize ();

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

(*   Misc.reset_symbol (); *)

    (* Typing *)
    let p = do_pass Typing.program "Typing" p pp true in

    (* Linear typing *)
    let p = do_pass Linear_typing.program "Linear Typing" p pp (not !no_mem_alloc) in

    if !print_types then Interface.Printer.print stdout;
    Modules.write itc;

    (* Causality check *)
    let p =
	do_silent_pass Causality.program "Causality check" p true in

    (* Initialization check *)
    let p =
      do_silent_pass Initialization.program "Initialization check" p !init in

    (* Mark nodes to be inlined *)
(*      let to_inline = List.map Misc.mk_longname !nodes_to_inline in
      let p = Inline.mark_calls_to to_inline p in
      let p = match !node_to_flatten with
      | None -> p
      | Some nn -> Inline.flatten nn p in
      if !verbose then comment "Inlining pre-pass";*)

    (* Inline marked nodes *)
(*      let p = do_pass Inline.program "Inlining" p pp true in  *)

   (* Automata memory sharing *)
    let p = do_pass Automata_mem.program "Automata memory sharing" p pp (not !no_mem_alloc) in

    (* Completion of partial definitions *)
    let p = do_pass Completion.program "Completion" p pp true in

    (* Automata *)
    let p = do_pass Automata.program "Automata" p pp true in

    (* Present *)
    let p = do_pass Present.program "Present" p pp true in

    (* Shared variables (last) *)
    let p = do_pass Last.program "Last" p pp true in

    (* Reset *)
    let reset_prog = if !use_new_reset_encoding then Reset_new.program else Reset.program in
    let p = do_pass reset_prog "Reset" p pp true in

    (* Every *)
    let p = do_pass Every.program "Every" p pp true in

    (* Merge and translate the heptagon program into the *)
    (* clocked data-flow language mini-ls *)
    let pp = Minils.Printer.print stdout in

    let p = Merge.program p in
    if !verbose then comment "Translation into clocked equations";
    Minils.Printer.print mlsc p;

    (* Annotation of expressions with their clock *)
    let p = Clocking.program p in

    (* Mls2dot.program "" p; *)

    (** Start of data-flow optimizations *)
    (* Normalization to maximize opportunities *)
    let p = do_pass Normalize.program "Normalization" p pp true in

    (* Back-end causality check. Only useful to check that *)
    (* we did not make any mistake during code generation *)
    let p =
      do_silent_pass Dfcausality.program "Post-pass causality check" p true in

    (* Check that the dataflow code is well initialized *)
    (*
      let p =
      do_silent_pass Init.program "Post-pass initialization check" p true in
    *)

    let sigali = List.mem "z3z" !target_languages in

    (* Boolean translation of enumerated values *)
  (*  let p =
      do_pass
        Boolean.program "Boolean transformation" p pp (!boolean or sigali) in
  *)

    (* Normalization to maximize opportunities *)
    let p = do_pass Normalize.program "Normalization" p pp true in

    (* Mls2dot.program "normalized_" p; *)

    let p =
      do_pass Deadcode.program "Deadcode removal" p pp !deadcode in

    (* Automata minimization *)
    let p = do_pass Tommls.program "Automata minimization" p pp !tomato in

    (* Common sub-expression elimination *)
    let p =
      do_pass Cmse.program "Common sub-expression elimination" p pp !cse in

    (* Removing intermediate equations *)
    let p =
      do_pass Intermediate.program "Intermediate-equations removal"
        p pp !intermediate in

    Mls2dot.program "optimized_" p;

    (* Splitting *)
    let p = do_pass Splitting.program "Splitting" p pp (not !no_mem_alloc) in

    (* Scheduling *)
    let scheduler = if !use_interf_scheduler then Schedule_interf.program else Schedule.program in
    let p = do_pass scheduler "Scheduling" p pp true in

    (* Memory allocation *)
    Interference.world.Interference.node_is_scheduled <- true;
    let p = do_pass Memalloc.program 
      "Interference graph building and Memory Allocation" p pp (not !no_mem_alloc) in

    (* Parametrized functions instantiation *)
    let p = do_pass Callgraph.program 
      "Parametrized functions instantiation" p pp true in

    Minils.Printer.print mlsnc p;

    (* Producing Object-based code *)
    let o = Translate.program p in
    if !verbose then comment "Translation into Object-based code";
    Obc.Printer.print obc o;

    let pp = Obc.Printer.print stdout in
      if !verbose then pp o;

    (* Translation into dataflow and sequential languages *)
    targets filename p o !target_languages;

    close_all_files ();

  with x -> close_all_files (); raise x
