(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
open Misc
open Names
open Ident
open Signature
open Minils
open Mls_utils
open Types

let ctrue = Name "true"
and cfalse = Name "false"

let equation (d_list, eq_list) e =
  let add_one_var ty d_list =
    let n = Ident.fresh "_v" in
    let d_list = (mk_var_dec ~clock:e.e_ck n ty) :: d_list in
      n, d_list
  in
    match e.e_ty with
      | Tprod ty_list ->
          let var_list, d_list =
            mapfold (fun d_list ty -> add_one_var ty d_list) d_list ty_list in
          let pat_list = List.map (fun n -> Evarpat n) var_list in
          let eq_list = (mk_equation (Etuplepat pat_list) e) :: eq_list in
          let e_list = List.map2
            (fun n ty -> mk_exp ~exp_ty:ty (Evar n)) var_list ty_list in
          let e = Eapp(mk_app Etuple, e_list, None) in
            (d_list, eq_list), e
      | _ ->
          let n, d_list = add_one_var e.e_ty d_list in
          let eq_list = (mk_equation (Evarpat n) e) :: eq_list in
            (d_list, eq_list), Evar n

let intro context e =
  match e.e_desc with
    | Evar n -> context, Evar n
    | _ -> equation context e

(* distribution: [(e1,...,ek) when C(n) = (e1 when C(n),...,ek when C(n))] *)
let rec whenc context e c n =
  let when_on_c c n e =
    { e with e_desc = Ewhen(e, c, n); e_ck = Con(e.e_ck, c, n) } in

  match e.e_desc with
    | Eapp({ a_op = Etuple } as app, e_list, r) ->
        let context, e_list =
          List.fold_right
            (fun e (context, e_list) -> let context, e = whenc context e c n in
             (context, e :: e_list))
            e_list (context, []) in
        context, { e with e_desc = Eapp (app, e_list, r);
                     e_ck = Con(e.e_ck, c, n) }
    | Econst { se_desc = Stuple se_list } ->
        let e_list = exp_list_of_static_exp_list se_list in
        let context, e_list =
          List.fold_right
            (fun e (context, e_list) -> let context, e = whenc context e c n in
               (context, e :: e_list))
            e_list (context, []) in
        context, { e with e_desc = Eapp (mk_app Etuple, e_list, None);
                     e_ck = Con(e.e_ck, c, n) }

          (* | Emerge _ -> let context, x = equation context e in
             context, when_on_c c n { e with e_desc = Evar(x) } *)
    | _ -> context, when_on_c c n e

(* transforms [merge x (c1, (e11,...,e1n));...;(ck, (ek1,...,ekn))] into *)
(* [merge x (c1, e11)...(ck, ek1),..., merge x (c1, e1n)...(ck, ekn)]    *)
let rec merge e x ci_a_list =
  let rec split ci_tas_list =
    match ci_tas_list with
      | [] | (_, _, []) :: _ -> [], []
      | (ci, b, a :: tas) :: ci_tas_list ->
          let ci_ta_list, ci_tas_list = split ci_tas_list in
          (ci, a) :: ci_ta_list, (ci, b, tas) :: ci_tas_list in
  let rec distribute ci_tas_list =
    match ci_tas_list with
      | [] | (_, _, []) :: _ -> []
      | (ci, b, (eo :: _)) :: _ ->
          let ci_ta_list, ci_tas_list = split ci_tas_list in
          let ci_tas_list = distribute ci_tas_list in
          (if b then
             { eo with e_desc = Emerge(x, ci_ta_list);
                 e_ck = e.e_ck; e_loc = e.e_loc }
           else
             merge e x ci_ta_list)
          :: ci_tas_list in
  let rec erasetuple ci_a_list =
    match ci_a_list with
      | [] -> []
      | (ci, { e_desc = Eapp({ a_op =  Etuple }, l, _) }) :: ci_a_list ->
          (ci, false, l) :: erasetuple ci_a_list
      | (ci, { e_desc = Econst { se_desc = Stuple se_list } }) :: ci_a_list ->
          let l = exp_list_of_static_exp_list se_list in
            (ci, false, l) :: erasetuple ci_a_list
      | (ci, e) :: ci_a_list ->
          (ci, true, [e]) :: erasetuple ci_a_list in
  let ci_tas_list = erasetuple ci_a_list in
  let ci_tas_list = distribute ci_tas_list in
  match ci_tas_list with
    | [e] -> e
    | l -> { e with e_desc = Eapp(mk_app Etuple, l, None) }

let ifthenelse context e1 e2 e3 =
  let context, n = intro context e1 in
  let n = (match n with Evar n -> n | _ -> assert false) in
  let context, e2 = whenc context e2 ctrue n in
  let context, e3 = whenc context e3 cfalse n in
    context, merge e1 n [ctrue, e2; cfalse, e3]

let const e c =
  let rec const = function
    | Cbase | Cvar { contents = Cindex _ } -> c
    | Con(ck_on, tag, x) ->
        Ewhen({ e with e_desc = const ck_on; e_ck = ck_on }, tag, x)
    | Cvar { contents = Clink ck } -> const ck in
  const e.e_ck

(* normal form for expressions and equations:                              *)
(* - e ::= op(e,...,e) | x | C | e when C(x)                               *)
(* - act ::= e | merge x (C1 -> act) ... (Cn -> act) | (act,...,act)       *)
(* - eq ::= [x = v fby e] | [pat = act ] | [pat = f(e1,...,en) every n     *)
(* - A-normal form: (e1,...,en) when c(x) = (e1 when c(x),...,en when c(x) *)
type kind = VRef | Exp | Act | Any

let function_args_kind = Exp
let merge_kind = Act

let rec constant e = match e.e_desc with
  | Econst _ -> true
  | Ewhen(e, _, _) -> constant e
  | Evar _ -> true
  | _ -> false

let add context expected_kind ({ e_desc = de } as e) =
  let up = match de, expected_kind with
    | (Evar _ | Eapp ({ a_op = Efield }, _, _)) , VRef -> false
    | _ , VRef -> true
    | Eapp ({ a_op = Efun n }, _, _),
        (Exp|Act) when is_op n -> false
    | ( Emerge _ | Eapp _ | Eiterator | Efby _ ), Exp -> true
    | ( Eapp({ a_op = Efun _ | Enode _ }, _, _)
      | Eiterator | Efby _ ), Act -> true
    | _ -> false in
  if up then
    let context, n = equation context e in
    context, { e with e_desc = n }
  else context, e

let rec translate kind context e =
  let context, e = match e.e_desc with
    | Emerge(n, tag_e_list) ->
        let context, ta_list =
          List.fold_right
            (fun (tag, e) (context, ta_list) ->
               let context, act = translate merge_kind context e in
               context, ((tag, act) :: ta_list))
            tag_e_list (context, []) in
        context, merge e n ta_list
    | Ewhen(e1, c, n) ->
        let context, e1 = translate kind context e1 in
        whenc context e1 c n
    | Efby(v, e1) ->
        let context, e1 = translate Act context e1 in
          fby kind context e v e1
    | Evar _ -> context, e
    | Econst c -> context, { e with e_desc = const e (Econst c) }
    | Estruct(l) ->
        let context, l =
          List.fold_right
            (fun (field, e) (context, field_desc_list) ->
               let context, e = translate Exp context e in
               context, ((field, e) :: field_desc_list))
            l (context, []) in
        context, { e with e_desc = Estruct l }
    | Eapp({ a_op = Eifthenelse }, [e1; e2; e3], _) ->
        let context, e1 = translate Any context e1 in
        let context, e2 = translate Act context e2 in
        let context, e3 = translate Act context e3 in
          ifthenelse context e1 e2 e3
    | Eapp(app, e_list, r) ->
        let context, e_list = translate_app kind context app.a_op e_list in
          context, { e with e_desc = Eapp(app, e_list, r) }
    | Eiterator (it, app, n, e_list, reset) ->
        let app =
          (match app.a_op with
             | Elambda(inp, outp, [], eq_list) ->
                let d_list, eq_list = translate_eq_list [] eq_list in
                  { app with a_op = Elambda(inp, outp, d_list, eq_list) }
             | _ -> app) in

        (* Add an intermediate equation for each array lit argument. *)
        let translate_iterator_arg_list context e_list =
          let add e context =
            let kind = match e.e_desc with
              | Econst { se_desc = Sarray _; } -> VRef
              | _ -> function_args_kind in
            translate kind context e in
          Misc.mapfold_right add e_list context in

        let context, e_list =
          translate_iterator_arg_list context e_list in
        context, { e with e_desc = Eiterator(it, app, n, e_list, reset) }
  in add context kind e

and translate_app kind context op e_list =
  match op, e_list with
    | (Efun _ | Enode _), e_list ->
        let context, e_list =
          translate_list function_args_kind context e_list in
        context, e_list
    | Etuple, e_list ->
        let context, e_list = translate_list kind context e_list in
          context, e_list
    | Efield, [e'] ->
        let context, e' = translate Exp context e' in
          context, [e']
    | Efield_update, [e1; e2] ->
        let context, e1 = translate VRef context e1 in
        let context, e2 = translate Exp context e2 in
          context, [e1; e2]
    | Earray, e_list ->
        let context, e_list = translate_list kind context e_list in
          context, e_list
    | Earray_fill, [e] ->
        let context, e = translate VRef context e in
          context, [e]
    | Eselect, [e'] ->
        let context, e' = translate VRef context e' in
          context, [e']
    | Eselect_dyn, e1::e2::idx ->
        let context, e1 = translate VRef context e1 in
        let context, idx = translate_list Exp context idx in
        let context, e2 = translate Exp context e2 in
        context, e1::e2::idx
    | Eupdate, [e1; e2]  ->
        let context, e1 = translate VRef context e1 in
        let context, e2 = translate Exp context e2 in
          context, [e1; e2]
    | Eselect_slice, [e'] ->
        let context, e' = translate VRef context e' in
        context, [e']
    | Econcat, [e1; e2] ->
        let context, e1 = translate VRef context e1 in
        let context, e2 = translate VRef context e2 in
        context, [e1; e2]

and translate_list kind context e_list =
  match e_list with
      [] -> context, []
    | e :: e_list ->
        let context, e = translate kind context e in
        let context, e_list = translate_list kind context e_list in
        context, e :: e_list

and fby kind context e v e1 =
  let mk_fby c e =
    mk_exp ~exp_ty:e.e_ty ~loc:e.e_loc (Efby(Some c, e)) in
  let mk_pre e =
    mk_exp ~exp_ty:e.e_ty ~loc:e.e_loc (Efby(None, e)) in
  match e1.e_desc, v with
    | Eapp({ a_op = Etuple } as app, e_list, r),
      Some { se_desc = Stuple se_list } ->
        let e_list = List.map2 mk_fby se_list e_list in
        let e = { e with e_desc = Eapp(app, e_list, r) } in
          translate kind context e
    | Econst { se_desc = Stuple se_list },
      Some { se_desc = Stuple v_list } ->
        let e_list = List.map2 mk_fby v_list
          (exp_list_of_static_exp_list se_list) in
        let e = { e with e_desc = Eapp(mk_app Etuple, e_list, None) } in
          translate kind context e
    | Eapp({ a_op = Etuple } as app, e_list, r), None ->
        let e_list = List.map mk_pre e_list in
        let e = { e with e_desc = Eapp(app, e_list, r) } in
          translate kind context e
    | Econst { se_desc = Stuple se_list }, None ->
        context, e1
    | _ ->
        let context, e1' =
          if constant e1 then context, e1
          else let context, n = equation context e1 in
          context, { e1 with e_desc = n } in
        context, { e with e_desc = Efby(v, e1') }

and translate_eq context eq =
  (* applies distribution rules *)
  (* [x = v fby e] should verifies that x is local *)
  (* [(p1,...,pn) = (e1,...,en)] into [p1 = e1;...;pn = en] *)
  let rec distribute ((d_list, eq_list) as context)
      ({ eq_lhs = pat; eq_rhs = e } as eq) =
    match pat, e.e_desc with
      | Evarpat(x), Efby _ when not (vd_mem x d_list) ->
          let (d_list, eq_list), n = equation context e in
          d_list,
          { eq with eq_rhs = { e with e_desc = n } } :: eq_list
      | Etuplepat(pat_list), Eapp({ a_op = Etuple }, e_list, _) ->
          let eqs = List.map2 mk_equation pat_list e_list in
          List.fold_left distribute context eqs
      | _ -> d_list, eq :: eq_list in

  let context, e = translate Any context eq.eq_rhs in
  distribute context { eq with eq_rhs = e }

and translate_eq_list d_list eq_list =
  List.fold_left
    (fun context eq -> translate_eq context eq)
    (d_list, []) eq_list

let translate_contract ({ c_eq = eq_list; c_local = d_list } as c) =
  let d_list,eq_list = translate_eq_list d_list eq_list in
  { c with
      c_local = d_list;
      c_eq = eq_list }

let translate_node ({ n_contract = contract;
                      n_local = d_list; n_equs = eq_list } as node) =
  let contract = optional translate_contract contract in
  let d_list, eq_list = translate_eq_list d_list eq_list in
  { node with n_contract = contract; n_local = d_list; n_equs = eq_list }

let program ({ p_nodes = p_node_list } as p) =
  { p with p_nodes = List.map translate_node p_node_list }
