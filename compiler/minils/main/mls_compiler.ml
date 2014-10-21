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

let pp p = if !verbose then Mls_printer.print stdout p

;; IFDEF HAS_CTRLNBAC THEN

(* NB: I localize file name determination logics for CtrlNbac output into this
   module, because its place is not in CtrlNbacGen... *)
(** [gen_n_output_ctrln p] translates the Minils program [p] into
    Controllable-Nbac format, and then output its nodes separately in files
    under a specific directory; typically, a node ["n"] in file ["f.ept"] is
    output into a file called "f_ctrln/n.nbac" *)
let gen_n_output_ctrln p =
  let nodes, p = CtrlNbacGen.gen p in
  let filename = filename_of_name (Names.modul_to_string p.Minils.p_modname) in
  let dir = clean_dir (build_path (filename ^"_ctrln")) in
  List.iter begin fun (node_name, node) ->
    let oc = open_out (dir ^"/"^ node_name ^".ctrln") in
    let fmt = Format.formatter_of_out_channel oc in
    CtrlNbac.AST.print_node ~print_header:print_header_info fmt node;
    close_out oc
  end nodes;
  p

let maybe_ctrln_pass p =
  let ctrln = List.mem "ctrln" !target_languages in
  let _p = pass "Controllable Nbac generation" ctrln gen_n_output_ctrln p pp in
  ()

;; ELSE

let maybe_ctrln_pass p = p

;; END

let compile_program p =
  (* Clocking *)
  let p =
    try pass "Clocking" true Clocking.program p pp
    with Errors.Error ->
      comment ~sep:"" "\nInfered clocks :\n";
      pp p;
      comment ~sep:"*** " ("Clocking failed.");
      if !print_types then Global_printer.print_interface Format.std_formatter;
      raise Errors.Error
  in

  if !print_types then Global_printer.print_interface Format.std_formatter;

  (* Level clocks *)
  let p = pass "Level clock" true Level_clock.program p pp in

  (* Dataglow minimization *)
  let p =
    let call_tomato = !tomato || (List.length !tomato_nodes > 0) in
    let p = pass "Extended value inlining" call_tomato Inline_extvalues.program p pp in
    pass "Data-flow minimization" call_tomato Tomato.program p pp in

(** TODO: re enable when ported to the new AST
  let p =
    pass "Automata minimization checks" true Tomato.tomato_checks p pp in
*)

  (* Normalize memories*)
  let p = pass "Normalize memories" true Normalize_mem.program p pp in

  (* Scheduling *)
  let p =
    if not !Compiler_options.use_old_scheduler then
      pass "Scheduling (with minimization of interferences)" true Schedule_interf.program p pp
    else
      pass "Scheduling" true Schedule.program p pp
  in

  let _p = maybe_ctrln_pass p in
  (* NB: XXX _p is ignored for now... *)

  let z3z = List.mem "z3z" !target_languages in
  let p = pass "Sigali generation" z3z Sigalimain.program p pp in
  (* Re-scheduling after sigali generation *)
  let p =
    if not !Compiler_options.use_old_scheduler then
      pass "Scheduling (with minimization of interferences)" z3z Schedule_interf.program p pp
    else
      pass "Scheduling" z3z Schedule.program p pp
  in


  (* Memory allocation *)
  let p = pass "Memory allocation" !do_mem_alloc Interference.program p pp in

  p
