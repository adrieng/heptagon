(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Compiler_utils
open Obc
open Minils
open Misc

type target_source =
  | Obc
  | Obc_no_params
  | Minils
  | Minils_no_params

type convert_fun =
  | Obc_fun of (Obc.program -> unit)
  | Mls_fun of (Minils.program -> unit)

let write_object_file p =
  let filename = (filename_of_name p.Minils.p_modname)^".epo" in
  let epoc = open_out_bin filename in
    comment "Generating of object file";
    output_value epoc p;
    close_out epoc

let write_obc_file p =
  let obc_name = (filename_of_name p.Obc.p_modname)^".obc" in
  let obc = open_out obc_name in
    comment "Generation of Obc code";
    Obc_printer.print obc p;
    close_out obc

let targets = [ "c", (Obc_no_params, Obc_fun Cmain.program);
                "obc", (Obc, Obc_fun write_obc_file);
                "obc_np", (Obc_no_params, Obc_fun write_obc_file);
                "epo", (Minils, Mls_fun write_object_file) ]

let generate_target p s =
  let source, convert_fun =
    (try List.assoc s targets
    with Not_found -> language_error s; raise Error) in
    match source, convert_fun with
      | Minils, Mls_fun convert_fun ->
          convert_fun p
      | Obc, Obc_fun convert_fun ->
          let o = Mls2obc.program p in
            convert_fun o
      | Minils_no_params, Mls_fun convert_fun ->
          let p_list = Callgraph_mapfold.program p in
            List.iter convert_fun p_list
      | Obc_no_params, Obc_fun convert_fun ->
          let p_list = Callgraph_mapfold.program p in
          let o_list = List.map Mls2obc.program p_list in
            List.iter convert_fun o_list

let program p =
  (* Translation into dataflow and sequential languages *)
  let targets =
    if !create_object_file then
      ["epo"]
    else
      match !target_languages with
        | [] -> ["obc"];
        | l -> l
  in
    List.iter (generate_target p) targets;
