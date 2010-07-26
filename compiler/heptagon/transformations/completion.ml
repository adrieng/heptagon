(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* complete partial definitions with [x = last(x)] *)

open Misc
open Heptagon
open Global_mapfold
open Hept_mapfold
open Idents


(* We first define a shallow pass,
  meant to be called at an automaton/present/switch level
  It'll collect the set of defined names among the handlers of the automaton/...
*)

(* We stop at the first level, it'll correspond to an handler *)
let block_collect funs env b =
  b, b.b_defnames

let gather f funs env x =
  let x, new_env = f funs Env.empty x in
  x, Env.union new_env env

(* We need to return the union of the defined names which is done with [gather],
  without traversing anything else.
  This funs_collect will stop directly if called on something else than
  blocks or handlers. *)
let funs_collect =
  { Hept_mapfold.defaults_stop with
      block = block_collect;
      switch_handler = gather Hept_mapfold.switch_handler;
      present_handler = gather Hept_mapfold.present_handler;
      state_handler = gather Hept_mapfold.state_handler; }



(* The real pass adding the needed equations *)

(* adds an equation [x = last(x)] for every partially defined variable *)
(* in a control structure *)
let complete_with_last defined_names local_defined_names eq_list =
  let last n ty = mk_exp (Elast n) ty in
  let equation n ty eq_list =
    (mk_equation (Eeq(Evarpat n, last n ty)))::eq_list in
  let d = Env.diff defined_names local_defined_names in
  Env.fold equation d eq_list


let block funs defnames b =
  let b, _ = Hept_mapfold.block funs Env.empty b in (*recursive call*)
  let added_eq = complete_with_last defnames b.b_defnames [] in
  { b with b_equs = b.b_equs @ added_eq; b_defnames = defnames }
  , defnames

let eqdesc funs _ ed = match ed with
  | Epresent _ | Eautomaton _ | Eswitch _ ->
      (* collect defined names with the special pass *)
      let ed, defnames =
        Hept_mapfold.eqdesc funs_collect Env.empty ed in
      (* add missing defnames *)
      Hept_mapfold.eqdesc funs defnames ed
  | _ -> raise Misc.Fallback

let funs = { Hept_mapfold.defaults with eqdesc = eqdesc; block = block; }

let program p = let p, _ = program_it funs Env.empty p in p

