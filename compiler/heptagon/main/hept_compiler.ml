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

let compile_impl pp p =
  (* Typing *)
  let p = do_pass Typing.program "Typing" p pp true in
    
    if !print_types then Interface.Printer.print stdout;
    
    (* Causality check *)
    let p = do_silent_pass Causality.program "Causality check" p true in
      
    (* Initialization check *)
    let p =
      do_silent_pass Initialization.program "Initialization check" p !init in

    (* Completion of partial definitions *)
    let p = do_pass Completion.program "Completion" p pp true in

    (* Automata *)
    let p = do_pass Automata.program "Automata" p pp true in

    (* Present *)
    let p = do_pass Present.program "Present" p pp true in

    (* Shared variables (last) *)
    let p = do_pass Last.program "Last" p pp true in

    (* Reset *)
    let p = do_pass Reset.program "Reset" p pp true in

    (* Every *)
    let p = do_pass Every.program "Every" p pp true in

      (* Return the transformed AST *)
      p


let compile_interface l =
  Interface.Type.main l;
  if !print_types then Interface.Printer.print stdout;
  l
