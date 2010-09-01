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

(** Definition of a target. A target starts either from
    dataflow code (ie Minils) or sequential code (ie Obc),
    with or without static parameters*)
type target =
  | Obc of (Obc.program -> unit)
  | Obc_no_params of (Obc.program -> unit)
  | Minils of (Minils.program -> unit)
  | Minils_no_params of (Minils.program -> unit)

(** Writes a .epo file for program [p]. *)
let write_object_file p =
  let filename = (filename_of_name p.Minils.p_modname)^".epo" in
  let epoc = open_out_bin filename in
    output_value epoc p;
    close_out epoc;
    comment "Generating of object file"

(** Writes a .epo file for program [p]. *)
let write_obc_file p =
  let obc_name = (filename_of_name p.Obc.p_modname)^".obc" in
  let obc = open_out obc_name in
    Obc_printer.print obc p;
    close_out obc;
    comment "Generation of Obc code"

let targets = [ "c", Obc_no_params Cmain.program;
                "obc", Obc write_obc_file;
                "obc_np", Obc_no_params write_obc_file;
                "epo", Minils write_object_file ]

let generate_target p s =
  let print_unfolded p_list =
    if !Misc.verbose then
      begin
        Format.eprintf "** Unfolding done **@.";
        List.iter (Mls_printer.print stderr) p_list;
      end in

  let target =
    (try List.assoc s targets
    with Not_found -> language_error s; raise Error) in
    match target with
      | Minils convert_fun ->
          convert_fun p
      | Obc convert_fun ->
          let o = Mls2obc.program p in
            convert_fun o
      | Minils_no_params convert_fun ->
          let p_list = Callgraph.program p in
            List.iter convert_fun p_list
      | Obc_no_params convert_fun ->
          let p_list = Callgraph.program p in
          let o_list = List.map Mls2obc.program p_list in
          print_unfolded p_list;
          if !Misc.verbose then
            begin
              Format.eprintf "** Translation to Obc done **@.";
              List.iter (Obc_printer.print_prog Format.err_formatter) o_list;
            end;
            List.iter convert_fun o_list

let program p =
  (* Translation into dataflow and sequential languages *)
  let targets =
    if !create_object_file then
      ["epo"]
    else
      match !target_languages with
        | [] -> ["obc"]; (* by default, generate obc file *)
        | l -> l
  in
    List.iter (generate_target p) targets
