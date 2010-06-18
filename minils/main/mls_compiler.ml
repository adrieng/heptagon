(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
open Misc
open Compiler_utils

let compile pp p =
  (* Clocking *)
  let p = do_silent_pass Clocking.program "Clocking" p true in

  (* Back-end causality check. Only useful to check that *)
  (* we did not make any mistake during code generation *)
  let p =
    do_silent_pass Dfcausality.program "Causality check" p true in

  (* Check that the dataflow code is well initialized *)
  let p =
    do_silent_pass Init.program "Initialization check" p !init in

  (* Normalization to maximize opportunities *)
  let p = do_pass Normalize.program "Normalization" p pp true in
    
  (* Scheduling *)
  let p = do_pass Schedule.program "Scheduling" p pp true in
    
  (* Parametrized functions instantiation *)
  let p = do_pass Callgraph.program 
    "Parametrized functions instantiation" p pp true in

    p
