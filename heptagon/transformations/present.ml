(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* removing present statements *)

(* $Id$ *)

open Misc
open Location
open Heptagon
open Initial

let rec translate_eq v eq =
  match eq.eq_desc with
    | Eswitch(e, switch_handlers) ->
        v, { eq with eq_desc =
            Eswitch(e, translate_switch_handlers switch_handlers) }
    | Epresent(present_handlers, block) ->
        v,
        translate_present_handlers present_handlers (translate_block block)
    | Ereset(eq_list, e) ->
        let v, eq_list = translate_eqs v eq_list in
        v, { eq with eq_desc = Ereset(eq_list, e) }
    | Eeq _ -> v, eq
    | Eautomaton _ -> assert false

and translate_eqs v eq_list =
  List.fold_left
    (fun (v, eq_list) eq ->
       let v, eq = translate_eq v eq in v, eq :: eq_list)
    (v, []) eq_list

and translate_block ({ b_local = v; b_equs = eq_list } as b) =
  let v, eq_list = translate_eqs v eq_list in
  { b with b_local = v; b_equs = eq_list }

and translate_switch_handlers handlers =
  let translate_switch_handler { w_name = n; w_block = b } =
    { w_name = n; w_block = translate_block b } in
  List.map translate_switch_handler handlers

and translate_present_handlers handlers cont =
  let translate_present_handler { p_cond = e; p_block = b } cont =
    let statefull = b.b_statefull or cont.b_statefull in
    mk_block ~statefull:statefull b.b_defnames 
      [mk_switch_equation ~statefull:statefull e [{ w_name = ptrue; w_block = b };
                           { w_name = pfalse; w_block = cont }]] in
  let b = List.fold_right translate_present_handler handlers cont in
  List.hd (b.b_equs)

let translate_contract ({ c_local = v; c_eq = eq_list} as c) =
  let v, eq_list = translate_eqs v eq_list in
  { c with c_local = v; c_eq = eq_list }

let node ({ n_local = v; n_equs = eq_list; n_contract = contract } as n) =
  let v, eq_list = translate_eqs v eq_list in
  let contract = optional translate_contract contract in
  { n with n_local = v; n_equs = eq_list; n_contract = contract }

let program ({ p_types = pt_list; p_nodes = n_list } as p) =
  { p with p_types = pt_list; p_nodes = List.map node n_list }
