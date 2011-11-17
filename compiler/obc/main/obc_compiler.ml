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

let pp p = if !verbose then Obc_printer.print stdout p

let compile_program p =

  (* Memory allocation application *)
  let p = pass "Application of Memory Allocation"
    (!do_mem_alloc or !do_linear_typing) Memalloc_apply.program p pp in

  (*Scalarize for wanting backends*)
  let p = pass "Scalarize" (!do_scalarize) Scalarize.program p pp in

  (*Simplify*)
  let p = pass "Simplify" (!do_simplify) Simplify.program p pp in

  (*Dead code removal*)
  let p = pass "Dead code removal"
    (!do_mem_alloc or !do_linear_typing) Deadcode.program p pp in

  (*Control optimization*)
  let p = pass "Control optimization" true Control.program p pp in

  p
