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
open Idents
open Signature
open Minils
open Mls_utils
open Mls_printer
open Types
open Clocks
open Pp_tools

let debug_tomato = false

let debug_do f = if debug_tomato then f () else ()

let rec exp e (eq_list, var_list) = match e.e_desc with
  | Evar _ | Econst _ -> (e, eq_list, var_list)
  | _ ->
      let (e_desc, eq_list, var_list) = match e.e_desc with
        | Evar _ | Econst _ -> assert false (* handled above *)
        | Efby (seo, e) ->
            let (e, eq_list, var_list) = intro_var e (eq_list, var_list) in
            Efby (seo, e), eq_list, var_list
        | Eapp (app, e_list, vi) ->
            let (e_list, eq_list, var_list) =
              intro_vars e_list (eq_list, var_list) in
            Eapp (app, e_list, vi), eq_list, var_list
        | Ewhen (e, cn, vi) ->
            let (e, eq_list, var_list) = intro_var e (eq_list, var_list) in
            Ewhen (e, cn, vi), eq_list, var_list
        | Emerge (vi, cnel) ->
            let e_list = List.map snd cnel in
            let e_list, eq_list, var_list =
              intro_vars e_list (eq_list, var_list) in
            let cnel = List.combine (List.map fst cnel) e_list in
            Emerge (vi, cnel), eq_list, var_list
        | Estruct fnel ->
            let e_list = List.map snd fnel in
            let e_list, eq_list, var_list =
              intro_vars e_list (eq_list, var_list) in
            let fnel = List.combine (List.map fst fnel) e_list in
            Estruct fnel, eq_list, var_list
        | Eiterator (it, app, se, e_list, vio) ->
            let (e_list, eq_list, var_list) =
              intro_vars e_list (eq_list, var_list) in
            Eiterator (it, app, se, e_list, vio), eq_list, var_list in
      ({ e with e_desc = e_desc; }, eq_list, var_list)

and intro_vars e_list (eq_list, var_list) =
  let acc e (e_list, eq_list, var_list) =
    let (e, eq_list, var_list) = intro_var e (eq_list, var_list) in
    (e :: e_list, eq_list, var_list) in
  List.fold_right acc e_list ([], eq_list, var_list)

and intro_var e (eq_list, var_list) =
  let (e, eq_list, var_list) = exp e (eq_list, var_list) in
  match e.e_desc with
    | Evar _ -> (e, eq_list, var_list)
    | _ ->
        let id = Idents.fresh "t" in
        let new_eq = mk_equation (Evarpat id) e
        and var_dc = mk_var_dec id e.e_ty in
        (mk_exp ~ty:e.e_ty (Evar id), new_eq :: eq_list, var_dc :: var_list)

let rec intro_vars_pat pat e (eq_list, var_list) = match pat, e.e_desc with
  | _, Eapp ({ a_op = Efun _ | Enode _; }, _, _) ->
      let (e, eq_list, var_list) = exp e (eq_list, var_list) in
      (mk_equation pat e :: eq_list, var_list)
  | Etuplepat pat, Econst { se_desc = Stuple se_list; se_ty = Tprod ty_list } ->
      let e_list =
        let mk se ty = mk_exp ~ty:ty (Econst se) in
        List.map2 mk se_list ty_list in
      List.fold_right2 intro_vars_pat pat e_list (eq_list, var_list)
  | Etuplepat pat_list, Eapp ({ a_op = Etuple; }, e_list, _) ->
      List.fold_right2 intro_vars_pat pat_list e_list (eq_list, var_list)
  | pat, _ ->
      let (e, eq_list, var_list) = exp e (eq_list, var_list) in
      (mk_equation pat e :: eq_list, var_list)

and mk_var_decs pat ty var_list = match pat, ty with
  | Evarpat ident, _ -> mk_var_dec ident ty :: var_list
  | Etuplepat pat_list, Tprod ty_list ->
      List.fold_right2 mk_var_decs pat_list ty_list var_list
  | _ -> assert false (* ill-typed *)

let eq eq (eq_list, var_list) =
  intro_vars_pat eq.eq_lhs eq.eq_rhs (eq_list, var_list)

let node nd =
  let nd = Elimtuples.node nd in
  debug_do (fun _ ->
              Format.printf "Detuplized node:@\n%a@." print_node nd);
  let (eq_list, var_list) = List.fold_right eq nd.n_equs ([], nd.n_local) in
  { nd with n_equs = eq_list; n_local = var_list; }

let program p = { p with p_nodes = List.map node p.p_nodes; }
