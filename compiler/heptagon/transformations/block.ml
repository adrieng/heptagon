(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* Removes the Eblock construction *)

(* To this mean, we will collect all equations and var dec
   and bring it up to the level above (a block).
   An Eblock is an equation and thus is always in a block. *)


open Heptagon
open Hept_mapfold

(** v_acc is the new local vars which were in lower levels,
    eq_acc contains all the equations *)

let eq funs (v_acc, eq_acc) eq = match eq.eq_desc with
  | Eblock b -> (* flatten it : add inside vars and eqs to the acc *)
      let b,_ = block_it funs ([],[]) b in
      eq, (b.b_local@v_acc, b.b_equs@eq_acc)
  | _ -> eq, (v_acc, eq::eq_acc) (*add current eq to the acc*)

let block funs _ b =
  let _, (v_acc, eq_acc) = Hept_mapfold.block funs ([],[]) b in
  {b with b_local = v_acc@b.b_local; b_equs = eq_acc},
  ([], [])

let program p =
  let funs =
    { defaults with block = block; eq = eq; } in
  let p, (v_acc, eq_acc) = Hept_mapfold.program funs ([], []) p in
  (* nothing should be left in the acc *)
  assert (v_acc = []);
  assert (eq_acc = []);
  p
