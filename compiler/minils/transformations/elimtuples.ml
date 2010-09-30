(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* This module removes tuple-patterns when possible.

   (x, y) = if b then (1, 2) else (3, 4);
   ->
   x = if b then 1 else 3;
   y = if b then 2 else 4;

   However, if f() is a function/node returning multiple values, the following
   equation stay the same:

   (x, y) = if b then (1, 2) else f(arg);
*)

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

(* raised when a multi-valued call is found *)
exception Call

(* never leaves the scope of a precise pattern, i.e. [e_list] never changes type
   during subsequent recursive calls. *)
let rec control e_list =
  let exp e e_list = match e.e_desc with
    | Eapp ({ a_op = Efun _ | Enode _; }, _, _) -> raise Call
    | Eapp ({ a_op = Etuple; }, arg_list, _) -> arg_list @ e_list
    | Econst { se_desc = Stuple arg_list; } ->
        List.map (fun se -> mk_exp ~ty:se.se_ty (Econst se)) arg_list
    | Eapp ({ a_op = Eifthenelse; } as op, [c; t; e], rst) ->
        let t_children = control [t]
        and e_children = control [e] in
        let add_condition t e =
          mk_exp ~ty:t.e_ty (Eapp (op, [c; t; e], rst)) in
        List.map2 add_condition t_children e_children
    | _ -> e :: e_list in
  List.fold_right exp e_list []

let rec eq equ eq_list = match equ.eq_lhs with
  | Evarpat _ -> equ :: eq_list
  | Etuplepat pat_list ->
      try
        let new_eqs = List.map2 mk_equation pat_list (control [equ.eq_rhs]) in
        List.fold_right eq new_eqs eq_list
      with Call -> equ :: eq_list

let node nd =
  let eq_list = List.fold_right eq nd.n_equs [] in
  { nd with n_equs = eq_list; }

let program p = { p with p_nodes = List.map node p.p_nodes; }
