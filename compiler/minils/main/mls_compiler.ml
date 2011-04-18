(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
open Misc
open Location
open Compiler_utils
open Compiler_options

let pp p = if !verbose then Mls_printer.print stdout p

let compile_program p =
  (* Clocking *)
  let p = pass "Clocking" true Clocking.program p pp in

  (* Check that the dataflow code is well initialized *)
  (*let p = silent_pass "Initialization check" !init Init.program p in *)

  (* Automata minimization *)
(*
  let p =
    let call_tomato = !tomato or (List.length !tomato_nodes > 0) in
    pass "Automata minimization" call_tomato Tomato.program p pp in
*)
(** TODO: re enable when ported to the new AST
  let p =
    pass "Automata minimization checks" true Tomato.tomato_checks p pp in
*)

  (* Scheduling *)
  let p = pass "Scheduling" true Schedule.program p pp in

  p
