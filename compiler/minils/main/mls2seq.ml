(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Compiler_utils

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
        one_target others
    | ("vhdl_df" | "vhdl") :: others ->
        let dirname = build_path (filename ^ "_vhdl") in
        let dir = clean_dir dirname in
        let vhdl = Mls2vhdl.translate (Filename.basename filename) p in
        Vhdl.print dir vhdl;
        one_target others *)
    | unknown_lg :: others -> unknown_lg :: one_target others
    | [] -> [] in
  one_target target_languages

(** Generation of a sequential target *)
let sequential_target filename o target_languages =
  let rec one_target = function
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

