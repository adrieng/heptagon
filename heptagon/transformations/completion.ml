(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* complete partial definitions with [x = last(x)] *)

(* $Id$ *)

open Location
open Ident
open Misc
open Heptagon
open Global

(* adds an equation [x = last(x)] for every partially defined variable *)
(* in a control structure *)
let complete_with_last defined_names local_defined_names eq_list =
  let last n ty =
    { e_desc = Elast(n); e_ty = ty; e_linearity = Linearity.NotLinear;
      e_loc = no_location } in
  let equation n ty eq_list =
    { eq_desc = Eeq(Evarpat(n), last n ty); eq_statefull = false;
      eq_loc = no_location } :: eq_list in
  let d = Env.diff defined_names local_defined_names in
  Env.fold equation d eq_list

let rec translate_eq eq =
  match eq.eq_desc with
    | Ereset(eq_list, e) ->
        { eq with eq_desc = Ereset(translate_eqs eq_list, e) }
    | Eeq(pat, e) ->
        { eq with eq_desc = Eeq(pat, e) }
    | Eswitch(e, switch_handlers) ->
        let defnames =
          List.fold_left
            (fun acc { w_block = { b_defnames = d } } -> Env.union acc d)
            Env.empty switch_handlers in
        let switch_handlers =
          List.map (fun ({ w_block = b } as handler) ->
                      { handler with w_block = translate_block defnames b })
            switch_handlers in
        { eq with eq_desc = Eswitch(e, switch_handlers) }
    | Epresent(present_handlers, b) ->
        let defnames =
          List.fold_left
            (fun acc { p_block = { b_defnames = d } } -> Env.union acc d)
            b.b_defnames present_handlers in
        let present_handlers =
          List.map (fun ({ p_block = b } as handler) ->
                      { handler with p_block = translate_block defnames b })
            present_handlers in
        let b = translate_block defnames b in
        {eq with eq_desc = Epresent(present_handlers, b)}
    | Eautomaton(state_handlers) ->
        let defnames =
          List.fold_left
            (fun acc { s_block = { b_defnames = d } } -> Env.union acc d)
            Env.empty state_handlers in
        let state_handlers =
          List.map (fun ({ s_block = b } as handler) ->
                      { handler with s_block = translate_block defnames b })
            state_handlers in
        { eq with eq_desc = Eautomaton(state_handlers) }

and translate_eqs eq_list = List.map translate_eq eq_list

and translate_block defnames
    ({ b_defnames = bdefnames; b_equs = eq_list } as b) =
  let eq_list = translate_eqs eq_list in
  let eq_list = complete_with_last defnames bdefnames eq_list in
  { b with b_equs = eq_list; b_defnames = defnames }

let translate_contract ({ c_eq = eqs } as c) =
  { c with c_eq = translate_eqs eqs }

let node ({ n_equs = eq_list; n_contract = contract } as n) =
  { n with
      n_equs = translate_eqs eq_list;
      n_contract = optional translate_contract contract }

let program ({ p_types = pt_list; p_nodes = n_list } as p) =
  { p with p_types = pt_list; p_nodes = List.map node n_list }
