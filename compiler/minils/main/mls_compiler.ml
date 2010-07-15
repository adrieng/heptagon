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

  (* Check that the dataflow code is well initialized *)
  (*let p = do_silent_pass Init.program "Initialization check" p !init in *)

  (* Normalization to maximize opportunities *)
  let p = do_pass Normalize.program "Normalization" p pp true in

  (* Scheduling *)
  let p = do_pass Schedule.program "Scheduling" p pp true in

  (* Parametrized functions instantiation *)
  (*let p = do_pass Callgraph_mapfold.program
    "Parametrized functions instantiation" p pp true in*)
  p
