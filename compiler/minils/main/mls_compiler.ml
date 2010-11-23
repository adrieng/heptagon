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

let compile pp p =
  (* Clocking *)
  let p = pass "Clocking" true Clocking.program p pp in

  (* Check that the dataflow code is well initialized *)
  (*let p = silent_pass "Initialization check" !init Init.program p in *)

  (* Iterator fusion *)
  let p = pass "Iterator fusion" !do_iterator_fusion Itfusion.program  p pp in

  (* Automata minimization *)
  let p =
    let call_tomato = !tomato or (List.length !tomato_nodes > 0) in
    pass "Automata minimization" call_tomato Tomato.program p pp in

  let p =
    pass "Automata minimization checks" true Tomato.tomato_checks p pp in

  (* Normalization to maximize opportunities *)
  let p = pass "Normalization" true Normalize.program p pp in

  (* Scheduling *)
  let p = pass "Scheduling" true Schedule.program p pp in

  p
