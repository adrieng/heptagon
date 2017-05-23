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

(** Definition of a target. A target starts either from
    dataflow code (ie Minils) or sequential code (ie Obc),
    with or without static parameters *)
type program_target =
  | Obc of (Obc.program -> unit)
  | Obc_no_params of (Obc.program -> unit)
  | Minils of (Minils.program -> unit)
  | Minils_no_params of (Minils.program -> unit)
  | Disabled_target

type interface_target =
  | IObc of (Obc.interface -> unit)
  | IMinils of (Minils.interface -> unit)

type target =
    { t_name : string;
      t_program : program_target;
      t_interface : interface_target;
      t_load_conf : unit -> unit }

let no_conf () = ()

let mk_target ?(interface=IMinils ignore) ?(load_conf = no_conf) name pt =
  { t_name = name; t_program = pt;
    t_interface = interface; t_load_conf = load_conf }

(** Writes a .epo file for program [p]. *)
let write_object_file p =
  let filename = (String.uncapitalize_ascii (Names.modul_to_string p.Minils.p_modname)) ^".epo" in
  let epoc = open_out_bin filename in
    output_value epoc p;
    close_out epoc;
    comment "Generating of object file"

(** Writes a .obc file for program [p]. *)
let write_obc_file p =
  let obc_name = (Names.modul_to_string p.Obc.p_modname)^".obc" in
  let obc = open_out obc_name in
    do_silent_pass "Obc serialization" (Obc_printer.print obc) p;
    close_out obc;
    comment "Generation of Obc code"


let java_conf () =
  Compiler_options.do_scalarize := true;
  ()

;; IFDEF ENABLE_CTRLN THEN
let ctrln_targets =
  [ mk_target "ctrln" (Minils_no_params ignore) ]
;; ELSE
let ctrln_targets =
  [ mk_target "ctrln" Disabled_target ]
;; ENDIF

let targets =
  [ mk_target ~interface:(IObc Cmain.interface) "c" (Obc_no_params Cmain.program);
    mk_target ~load_conf:java_conf "java" (Obc Java_main.program);
    mk_target ~load_conf:java_conf "java14" (Obc Java14_main.program);
    mk_target "z3z" (Minils_no_params ignore);
    mk_target "obc" (Obc write_obc_file);
    mk_target "obc_np" (Obc_no_params write_obc_file);
    mk_target "epo" (Minils write_object_file) ]
  @ ctrln_targets

let find_target s =
  try
    List.find (fun t -> t.t_name = s) targets
  with
      Not_found -> language_error s; raise Errors.Error


let generate_target p out s =
(*  let print_unfolded p_list =
    comment "Unfolding";
    if !Compiler_options.verbose
    then List.iter (Mls_printer.print stderr) p_list in*)
  let { t_program = program; t_name = name } = find_target s in
  let callgraph p = do_silent_pass "Callgraph" Callgraph.program p in
  let mls2obc p = do_silent_pass "Translation from MiniLS" Mls2obc.program p in
  let mls2obc_list p_l = do_silent_pass "Translation from MiniLS" (List.map Mls2obc.program) p_l in
  match program with
    | Minils convert_fun ->
        do_silent_pass "Code generation from MiniLS" convert_fun p
    | Obc convert_fun ->
        let o = mls2obc p in
        let o = Obc_compiler.compile_program out o in
        do_silent_pass "Code generation from Obc" convert_fun o
    | Minils_no_params convert_fun ->
        let p_list = callgraph p in
        do_silent_pass "Code generation from Minils (w/o params)" (List.iter convert_fun) p_list
    | Obc_no_params convert_fun ->
        let p_list = callgraph p in
        let o_list = mls2obc_list p_list in
        let o_list = List.map (Obc_compiler.compile_program out) o_list in
        do_silent_pass "Code generation from Obc (w/o params)"         List.iter convert_fun o_list
    | Disabled_target ->
        warn "ignoring unavailable target `%s'." name

let generate_interface i s =
  let target = (find_target s).t_interface  in
  match target with
    | IObc convert_fun ->
      let o = do_silent_pass "Translation into Obc (interfaces)" Mls2obc.interface i in
      convert_fun o
    | IMinils convert_fun -> convert_fun i

let load_conf () =
  List.iter (fun s -> (find_target s).t_load_conf ()) !target_languages;
  try
    check_options ()
  with Arg.Bad m -> raise (Arg.Bad ("After loading target configurations: "^m))

(** Translation into dataflow and sequential languages, defaults to obc. *)
let program p out =
  let targets = match !target_languages with
    | [] -> ["obc"] (* by default, generate obc file *)
    | l -> l in
  let targets = if !create_object_file then "epo"::targets else targets in
  List.iter (generate_target p out) targets

let interface i =
  let targets = match !target_languages with
    | [] -> [] (* by default, generate obc file *)
    | l -> l in
  List.iter (generate_interface i) targets
