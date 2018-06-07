(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(* Nicolas Berthier, SUMO, INRIA                                       *)
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

let pp out p = if !verbose then Mls_printer.print out p

;; IFDEF ENABLE_CTRLN THEN

(* NB: I localize file name determination logics for CtrlNbac output into this
   module, because its place is not in CtrlNbacGen... *)
(** [gen_n_output_ctrln p] translates the Minils program [p] into
    Controllable-Nbac format, and then output its nodes separately in files
    under a specific directory; typically, a node ["n"] in file ["f.ept"] is
    output into a file called "f_ctrln/n.nbac" *)
let gen_n_output_ctrln p =

  (* Main generation procedure. *)
  let nodes, p = CtrlNbacGen.gen p in

  (* Save the controller module. *)
  Ctrln_utils.save_controller_modul_for p.Minils.p_modname;

  (* Output Controllable-Nbac contoller. *)
  ignore (clean_dir (Ctrln_utils.dirname_for_modul p.Minils.p_modname));
  List.iter begin fun (node_name, node) ->
    let oc = open_out (Ctrln_utils.ctrln_for_node node_name) in
    let fmt = Format.formatter_of_out_channel oc in
    CtrlNbac.AST.print_node ~print_header:print_header_info fmt node;
    close_out oc
  end nodes;
  p

let maybe_ctrln_pass p pp =
  let ctrln = List.mem "ctrln" !target_languages in
  pass "Controllable Nbac generation" ctrln gen_n_output_ctrln p pp

;; ELSE

let maybe_ctrln_pass p pp = p

;; END

let compile_program p log_c =

  let pp p = pp log_c p in

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
    match !Compiler_options.use_old_scheduler,
          !Compiler_options.use_simple_scheduler with
    | false, false ->
       pass "Scheduling (with minimization of interferences)"
            true Schedule_interf.program p pp
    | true, false ->
       pass "Scheduling" true Schedule.program p pp
    | _, true ->
       pass "Scheduling (simple)" true Schedule_simple.program p pp
  in

  let z3z = List.mem "z3z" !target_languages in
  let ctrln = List.mem "ctrln" !target_languages in
  let ctrl = z3z || ctrln in
  if z3z && ctrln then
    warn "ignoring target `ctrln' (incompatible with target `z3z').";

  let p = maybe_ctrln_pass p pp in
  let p = pass "Sigali generation" z3z Sigalimain.program p pp in

  (* Re-scheduling after generation *)
  let p =
    match !Compiler_options.use_old_scheduler,
          !Compiler_options.use_simple_scheduler with
    | false, false ->
      pass "Scheduling (with minimization of interferences)" ctrl Schedule_interf.program p pp
    | true, false ->
      pass "Scheduling" ctrl Schedule.program p pp
    | _, true ->
       pass "Scheduling (simple)" ctrl Schedule_simple.program p pp
  in

  (* Memory allocation *)
  let p = pass "Memory allocation" !do_mem_alloc Interference.program p pp in

  p
