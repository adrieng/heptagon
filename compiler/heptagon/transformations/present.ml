(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* removing present statements *)

open Heptagon
open Hept_utils
open Hept_mapfold

let translate_present_handlers handlers cont =
  let translate_present_handler { p_cond = e; p_block = b } cont =
    let stateful = b.b_stateful or cont.b_stateful in
      mk_block ~stateful:stateful ~defnames:b.b_defnames
        [mk_switch_equation e
           [{ w_name = Initial.ptrue; w_block = b };
            { w_name = Initial.pfalse; w_block = cont }]] in
  let b = List.fold_right translate_present_handler handlers cont in
    (List.hd (b.b_equs)).eq_desc

let eqdesc funs acc eqd =
  let eqd, _ = Hept_mapfold.eqdesc funs acc eqd in
    match eqd with
      | Epresent(ph, b) -> translate_present_handlers ph b, acc
      | _ -> eqd, acc

let program p =
  let funs = { Hept_mapfold.defaults with eqdesc = eqdesc } in
  let p, _ = Hept_mapfold.program_it funs false p in
    p

