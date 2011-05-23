(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Clocks
open Minils

(* Any clock variable left after clocking is free and should be set to level_ck.
   Since inputs and outputs are grounded to Cbase, this append when
   no data dependence exists between an expression and the inputs/outputs.*)

(* We are confident that it is sufficient to unify level_ck with base_ck
   for expressions having a base_ck == Cvar.
   The other ones are coming from one like this one,
   indeed if it was Con (Cvar,c,x) x would have to be defined with an expression of clock Cvar.*)

let eq _ acc eq =
  let e = eq.eq_rhs in
  let _ = match ck_repr e.e_base_ck with
    | Cvar {contents = Cindex _} -> unify_ck e.e_base_ck e.e_level_ck
    | _ -> ()
  in
  eq,acc (* no recursion since in minils exps are not recursive *)

let program p =
  let funs = { Mls_mapfold.defaults with Mls_mapfold.eq = eq } in
  let p, _ = Mls_mapfold.program_it funs [] p in
  p