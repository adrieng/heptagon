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
open Global_printer
open Types
open Clocks
open Pp_tools

module UseCounts =
struct
  type use =
    | Clock
    | Reset
    | Var of int

  let find_uses ident use_counts =
    try Env.find ident use_counts
    with Not_found -> Var 0

  let add_var_use ident use_counts =
    let use = match find_uses ident use_counts with
      | Var x -> Var (x + 1)
      | use -> use in
    Env.add ident use use_counts

  let add_clock_use ident use_counts = Env.add ident Clock use_counts

  let add_reset_use ident use_counts = Env.add ident Reset use_counts

  let factorable ident e use_count =
    let uses = find_uses ident use_count in
    match uses with
      | Clock | Reset -> false
      | Var i -> i < 2 || (match e.e_desc with Econst _ -> true | _ -> false)

  let edesc funs use_counts edesc =
    let (edesc, use_counts) = Mls_mapfold.edesc funs use_counts edesc in
    let use_counts = match edesc with
      | Evar vi -> add_var_use vi use_counts
      | Emerge (vi, _) -> add_clock_use vi use_counts
      | Ewhen (_, _, vi) -> add_clock_use vi use_counts
      | Eapp (_, _, Some vi) | Eiterator (_, _, _, _, Some vi) ->
          add_reset_use vi use_counts
      | _ -> use_counts in
    (edesc, use_counts)

  let node nd =
    let funs = { Mls_mapfold.defaults with Mls_mapfold.edesc = edesc; } in
    snd (Mls_mapfold.node_dec funs Env.empty nd)
end

module InlineSingletons =
struct
  let exp funs subst exp =
    let (exp, subst) = Mls_mapfold.exp funs subst exp in
    match exp.e_desc with
      | Evar vi -> (try Env.find vi subst with Not_found -> exp), subst
      | _ -> (exp, subst)

  let inline_node subst nd =
    let funs = { Mls_mapfold.defaults with Mls_mapfold.exp = exp; } in
    fst (Mls_mapfold.node_dec funs subst nd)

  let inline_exp subst e =
    let funs = { Mls_mapfold.defaults with
                   Mls_mapfold.exp = exp; } in
    fst (Mls_mapfold.exp_it funs subst e)
end

let debug_subst subst =
  Env.iter
    (fun id e -> Format.printf "%a -> @[%a@]@." print_ident id print_exp e)
    subst

let rec close_subst subst =
  let close_binding id e subst =
    let e = InlineSingletons.inline_exp subst e in
    let s = Env.add id e Env.empty in
    let inline id e subst =
      Env.add id (InlineSingletons.inline_exp s e) subst in
    Env.fold inline subst Env.empty in
  Env.fold close_binding subst subst

let node nd =
  (* Removes unused var_decs from a node *)
  let filter_var_decs nd =
    let add eq iset = List.fold_right IdentSet.add (Vars.def [] eq) iset in
    let iset = List.fold_right add nd.n_equs IdentSet.empty in
    let add_if_useful vd local =
      if IdentSet.mem vd.v_ident iset then vd :: local else local in
    { nd with n_local = List.fold_right add_if_useful nd.n_local [] } in

  let use_counts = UseCounts.node nd in

  let add_reset rst e = e in

  let is_output id = List.exists (fun vd -> vd.v_ident = id) nd.n_output in

  let (eq_list, subst) =
    let add_to_subst eq (eq_list, subst) =
      match (eq.eq_lhs, eq.eq_rhs.e_desc) with
        (* do not inline tuple patterns  *)
        | Etuplepat _, _ -> (eq :: eq_list, subst)
        | _ ->
            let id_list = Vars.def [] eq in
            let e_list, rst, unsafe = match eq.eq_rhs.e_desc with
            (* | Eapp ({ a_op = Etuple; a_unsafe = unsafe; }, e_list, rst)
               -> *)
            (*     e_list, rst, unsafe *)
               | _ -> [eq.eq_rhs], None, false in

            (* Walk over variables/exps couples of eq, gathering equations to
               be inlined.
               POSTCOND: id_list and e_list only contains non-singleton vars,
               subst is enriched with singleton vars encountered. *)
            let (id_list, e_list, subst) =
              let add_if_needed id e (id_list, e_list, subst) =
                if UseCounts.factorable id e use_counts && not (is_output id)
                then (id_list, e_list, Env.add id e subst) (* to be expanded *)
                else (id :: id_list, e :: e_list, subst) in
              List.fold_right2 add_if_needed id_list e_list ([], [], subst) in

            assert (List.length id_list = List.length e_list);

            match id_list, e_list with
              | [], [] -> (eq_list, subst)
              | [id], [e] ->
                  (mk_equation (Evarpat id) (add_reset rst e) :: eq_list, subst)
              | _ ->
                  let pat =
                    Etuplepat (List.map (fun id -> Evarpat id) id_list) in

                  let eq =
                    mk_equation pat
                      { eq.eq_rhs with e_desc =
                          Eapp ({ a_op = Etuple;
                                  a_params = [];
                                  a_unsafe = unsafe; }, e_list, rst); } in
                  (eq :: eq_list, subst) in
    List.fold_right add_to_subst nd.n_equs ([], Env.empty) in

  let nd = { nd with n_equs = eq_list; } in

  (* Format.printf "Node:@\n%a@\n" print_node nd; *)

  let subst = close_subst subst in

  (* debug_subst subst; *)

  let nd = InlineSingletons.inline_node subst nd in

  (* Format.printf "Node:@\n%a@\n" print_node nd; *)

  let nd = filter_var_decs nd in

  nd
