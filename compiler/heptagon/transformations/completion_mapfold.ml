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
open Ident

(* adds an equation [x = last(x)] for every partially defined variable *)
(* in a control structure *)
let complete_with_last defined_names local_defined_names eq_list =
  let last n ty = mk_exp (Elast n) ty in
  let equation n ty eq_list =
    (mk_equation (Eeq(Evarpat n, last n ty)))::eq_list
  in
  let d = Env.diff defined_names local_defined_names in
    Env.fold equation d eq_list

let block funs (defnames,collect)  b =
  if collect then
    b, (b.b_defnames, collect)
  else
    let b, _ = Hept_mapfold.block funs (Env.empty, false) b in
    let added_eq = complete_with_last defnames b.b_defnames [] in
      { b with b_equs = b.b_equs @ added_eq; b_defnames = defnames },
  (Env.empty, false)

let eqdesc funs _ ed =
  match ed with
    | Epresent _ | Eautomaton _ | Eswitch _ ->
        (* collect defined names *)
        let ed, (defnames, _) = Hept_mapfold.eqdesc funs (Env.empty, true) ed in
          (* add missing defnames *)
          Hept_mapfold.eqdesc funs (defnames, false) ed

    | _ -> raise Misc.Fallback

let gather (acc, collect) (local_acc, collect) =
  Env.union local_acc acc, collect

let program p =
  let funs =
    { Hept_mapfold.defaults
      with eqdesc = eqdesc; block = block;
           switch_handler = it_gather gather Hept_mapfold.switch_handler;
           present_handler = it_gather gather Hept_mapfold.present_handler;
           state_handler = it_gather gather Hept_mapfold.state_handler; } in
  let p, _ = program_it funs (Env.empty, false) p in
    p

