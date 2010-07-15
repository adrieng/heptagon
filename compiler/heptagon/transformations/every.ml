(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* removing complex reset expressions :
   equations
   x = (f every e) e'
   -->
   r = e;
   x = (f every r) e'
*)

open Misc
open Ident
open Heptagon
open Reset

(*
  let defnames m n d =
  let rec loop acc k = if k < n then loop (S.add m.(k) acc) (k+1) else acc in
  loop d 0
*)

let statefull eq_list = List.exists (fun eq -> eq.eq_statefull) eq_list

let is_var = function
  | { e_desc = Evar _ } -> true
  | _ -> false

let rec translate_eq v acc_eq_list eq =
  match eq.eq_desc with
    | Eeq(pat, e) ->
        let v,acc_eq_list,e = translate v acc_eq_list e in
        v, { eq with eq_desc = Eeq(pat, e) } :: acc_eq_list
    | Eswitch(e, tag_block_list) ->
        let v,acc_eq_list,e = translate v acc_eq_list e in
        let tag_block_list, acc_eq_list =
          translate_switch acc_eq_list tag_block_list in
        v, { eq with eq_desc = Eswitch(e, tag_block_list) } :: acc_eq_list
    | Ereset _ | Epresent _ | Eautomaton _ -> assert false

and translate_eqs v acc_eq_list eq_list =
  List.fold_left
    (fun (v,acc_eq_list) eq ->
       translate_eq v acc_eq_list eq) (v,acc_eq_list) eq_list

and translate_switch acc_eq_list switch_handlers =

  let body {w_name = c;
            w_block = ({ b_local = lv; b_defnames = d; b_equs = eqs } as b)} =
    let lv,eqs = translate_eqs lv [] eqs in
    { w_name = c;
      w_block = { b with b_local = lv; b_defnames = d; b_equs = eqs } } in

  let rec loop switch_handlers =
    match switch_handlers with
        [] -> []
      | handler :: switch_handlers ->
          (body handler) :: (loop switch_handlers) in

  loop switch_handlers, acc_eq_list

and translate v acc_eq_list e =
  match e.e_desc with
      Econst _ | Evar _ | Elast _ | Efby _ | Epre _ -> v,acc_eq_list,e
    | Eapp (op, e_list, Some re) when not (is_var re) ->
        let v, acc_eq_list,re = translate v acc_eq_list re in
        let n, v, acc_eq_list = equation v acc_eq_list re in
        let v, acc_eq_list, e_list = translate_list v acc_eq_list e_list in
        let re = { re with e_desc = Evar(n) } in
        v,acc_eq_list,
          { e with e_desc = Eapp (op, e_list, Some re) }
    | Eiterator(it, op, n, e_list, Some re) when not (is_var re) ->
        let v, acc_eq_list,re = translate v acc_eq_list re in
        let x, v, acc_eq_list = equation v acc_eq_list re in
        let v, acc_eq_list, e_list = translate_list v acc_eq_list e_list in
        let re = { re with e_desc = Evar x } in
        v,acc_eq_list,
          { e with e_desc = Eiterator(it, op, n, e_list, Some re) }
    | Eapp(op, e_list, r) ->
        let v, acc_eq_list, e_list = translate_list v acc_eq_list e_list in
        v, acc_eq_list,
        { e with e_desc = Eapp(op, e_list, r) }
    | Eiterator(it, op, n, e_list, r)  ->
        let v, acc_eq_list, e_list = translate_list v acc_eq_list e_list in
        v, acc_eq_list,
        { e with e_desc = Eiterator(it, op, n, e_list, r) }
    | Estruct(e_f_list) ->
        let v,acc_eq_list,e_f_list =
          List.fold_left
            (fun (v,acc_eq_list,acc_e_f) (f,e) ->
               let v,acc_eq_list,e = translate v acc_eq_list e in
               (v,acc_eq_list,(f,e)::acc_e_f))
            (v,acc_eq_list,[]) e_f_list in
        v,acc_eq_list,
        { e with e_desc = Estruct(List.rev e_f_list) }

and translate_list v acc_eq_list e_list =
  let v,acc_eq_list,acc_e =
    List.fold_left
      (fun (v,acc_eq_list,acc_e) e ->
         let v,acc_eq_list,e = translate v acc_eq_list e in
         (v,acc_eq_list,e::acc_e))
      (v,acc_eq_list,[]) e_list in
  v,acc_eq_list,List.rev acc_e

let translate_contract ({ c_local = v;
                          c_eq = eq_list;
                          c_assume = e_a;
                          c_enforce = e_g } as c) =
  let v,acc_eq,e_a = translate v [] e_a in
  let v,acc_eq,e_g = translate v acc_eq e_g in
  let v, eq_list = translate_eqs v acc_eq eq_list in
  { c with
      c_local = v;
      c_eq = eq_list;
      c_assume = e_a;
      c_enforce = e_g }

let node ({ n_local = v; n_equs = eq_list; n_contract = contract } as n) =
  let contract = optional translate_contract contract in
  let v, eq_list = translate_eqs v [] eq_list in
  { n with n_local = v; n_equs = eq_list; n_contract = contract }

let program ({ p_types = pt_list; p_nodes = n_list } as p) =
  { p with p_types = pt_list; p_nodes = List.map node n_list }
