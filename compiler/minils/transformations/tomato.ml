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
open Mls_compare

(* Data-flow minimization on MiniLS:

   1. Put each equation into a big map. It maps variable names to triples (class_id * truncated
   expression * class_id list). Initially, each local variable is in the same class.

   2. Compute the new class_id of each equation: two equations are in the same class if they are
   equal and have the same child equations.

   3. If anything has changed: go to 2

   4. Reconstruct: one equation for one equivalence class.
*)

module OrderedInts =
struct
  type t = int
  let compare = Pervasives.compare
end

module IntSet = Set.Make(OrderedInts)
module IntMap = Map.Make(OrderedInts)

module TomEnv =
struct

  module PatMap = Map.Make(struct
    type t = pat
    let compare = pat_compare
  end)

  type class_ref =
    | Cr_plain of ident
    | Cr_input of extvalue (* we record the full expression for convenience *)

  type eq_repr =
      {
        mutable er_class : int;
        er_pattern : pat;
        er_head : exp;
        er_children : class_ref list;
      }

  type tom_env = eq_repr PatMap.t

  open Mls_printer

  let print_class_ref fmt cr = match cr with
    | Cr_plain id -> print_ident fmt id
    | Cr_input w -> print_extvalue fmt w

  let debug_tenv fmt tenv =
    let debug pat repr =
      Format.fprintf fmt "%a => @[class %d,@ pattern %a,@ head { %a },@ children %a@]@."
        print_pat pat
        repr.er_class
        print_pat repr.er_pattern
        print_exp repr.er_head
        (print_list_r print_class_ref "[" ";" "]") repr.er_children
    in
    PatMap.iter debug tenv
end

open TomEnv

let gen_var = Idents.gen_var ~reset:false "tomato"

let dummy_extvalue = mk_extvalue ~ty:Initial.tint (Wvar (gen_var "dummy"))

let initial_class = 0

let concat_idents id1 id2 = gen_var (Idents.name id1 ^ "_" ^ Idents.name id2)

let symbol_for_int i =
  if i > 25
  then "a" ^ string_of_int i
  else String.make 1 (Char.chr (Char.code 'a' + i))

(*******************************************************************)
(* Construct an initial minimization environment                   *)
(*******************************************************************)

let rec add_equation is_input (tenv : tom_env) eq =
  let add_clause (cn, w) class_id_list =
    let class_id_list, w = extvalue is_input w class_id_list in
    class_id_list, (cn, w) in

  let ed, class_id_list = match eq.eq_rhs.e_desc with
    | Eextvalue w ->
      let class_id_list, w = extvalue is_input w [] in
      Eextvalue w, class_id_list
    | Eapp (app, w_list, rst) ->
      let class_id_list, w_list = mapfold_right (extvalue is_input) w_list [] in
      Eapp (app, w_list, rst), class_id_list
    | Efby (seo, w) ->
      let class_id_list, w = extvalue is_input w [] in
      Efby (seo, w), class_id_list
    | Ewhen _ -> assert false (* TODO *)
    | Emerge (vi, clause_list) ->
      let class_id_list, clause_list = mapfold_right add_clause clause_list [] in
      Emerge (vi, clause_list), class_id_list
    | Eiterator (it, app, se, partial_w_list, w_list, rst) ->
      let class_id_list, partial_w_list = mapfold_right (extvalue is_input) partial_w_list [] in
      let class_id_list, w_list = mapfold_right (extvalue is_input) w_list class_id_list in
      Eiterator (it, app, se, partial_w_list, w_list, rst), class_id_list
    | Estruct field_val_list ->
      let class_id_list, field_val_list = mapfold_right add_clause field_val_list [] in
      Estruct field_val_list, class_id_list
  in

  let eq_repr =
    {
      er_class = initial_class;
      er_pattern = eq.eq_lhs;
      er_head = { eq.eq_rhs with e_desc = ed; };
      er_children = class_id_list;
    }
  in

  PatMap.add eq.eq_lhs eq_repr tenv

and extvalue is_input w class_id_list = match w.w_desc with
  | Wvar v ->
    (if is_input v then Cr_input w else Cr_plain v)
    :: class_id_list, dummy_extvalue
  | _ -> class_id_list, w

(***********************************************************************)
(* Compute the next equivalence classes for a minimization environment *)
(***********************************************************************)

module EqClasses = Map.Make(
  struct
    type t = exp * int option list

    let unsafe { e_desc = ed; _ } = match ed with
      | Eapp (app, _, _) | Eiterator (_, app, _, _, _, _) -> app.a_unsafe
      | _ -> false

    let compare (e1, cr_list1) (e2, cr_list2) =
      let cr = Mls_compare.exp_compare e1 e2 in
      if cr <> 0 then cr
      else
        if unsafe e1 then 1
        else
          (if unsafe e2 then -1 else list_compare Pervasives.compare cr_list1 cr_list2)
  end)

let compute_new_class tenv =
  let fresh_id, get_id = let id = ref 0 in ((fun () -> incr id; !id), (fun () -> !id)) in

  let add_eq_repr _ eqr classes =
    let map_class_ref cref = match cref with
      | Cr_input _ -> None
      | Cr_plain v ->
        let er = PatMap.find (Evarpat v) tenv in
        Some er.er_class in
    let children = List.map map_class_ref eqr.er_children in

    let key = (eqr.er_head, children) in
    let id = try EqClasses.find key classes with Not_found -> fresh_id () in
    eqr.er_class <- id;
    EqClasses.add (eqr.er_head, children) id classes

  in

  let classes = PatMap.fold add_eq_repr tenv EqClasses.empty in

  (get_id (), tenv)

let rec separate_classes tenv =
  let rec fix (id, tenv) =
    Format.eprintf "New tenv %d:\n%a@." id debug_tenv tenv;
    let new_id, tenv = compute_new_class tenv in
    if new_id = id then tenv else fix (new_id, tenv)
  in
  fix (compute_new_class tenv)

(*******************************************************************)
(* Regroup classes from a minimization environment                 *)
(*******************************************************************)

let rec compute_classes tenv =
  let rec add_eq_repr _ repr cenv =
    let repr_list = try IntMap.find repr.er_class cenv with Not_found -> [] in
    IntMap.add repr.er_class (repr :: repr_list) cenv in
  PatMap.fold add_eq_repr tenv IntMap.empty

(********************************************************************)
(* Reconstruct a list of equation from a set of equivalence classes *)
(********************************************************************)

let rec reconstruct (((tenv : tom_env), cenv) as env) =
  let reconstruct_class id eq_repr_list eq_list =
    assert (List.length eq_repr_list > 0);

    let repr = List.hd eq_repr_list in

    let e =
      let ed = reconstruct_exp_desc (tenv, cenv) repr.er_head.e_desc repr.er_children in
      let ck = reconstruct_clock env repr.er_head.e_base_ck in
      let level_ck =
        reconstruct_clock env repr.er_head.e_level_ck in (* not strictly needed, done for
                                                            consistency reasons *)
      let ct = reconstruct_clock_type env repr.er_head.e_ct in
      { repr.er_head with e_desc = ed; e_base_ck = ck; e_level_ck = level_ck; e_ct = ct; } in

    let pat = pattern_name_for_id env repr.er_head.e_ty id in

    mk_equation pat e :: eq_list in
  IntMap.fold reconstruct_class cenv []

and reconstruct_exp_desc ((tenv : tom_env), (cenv : eq_repr list IntMap.t) as env) headd children =
  let reconstruct_clauses clause_list =
    let (qn_list, w_list) = List.split clause_list in
    let w_list = reconstruct_extvalues env w_list children in
    List.combine qn_list w_list in

  match headd with
  | Eextvalue w ->
    let w = assert_1 (reconstruct_extvalues env [w] children) in
    Eextvalue w
  | Efby (ini, w) ->
    let w = assert_1 (reconstruct_extvalues env [w] children) in
    Efby (ini, w)
  | Eapp (app, w_list, rst) ->
    Eapp (app, reconstruct_extvalues env w_list children, optional (new_ident_for env) rst)
  | Ewhen _ -> assert false (* TODO *)
  | Emerge (ck_x, clause_list) ->
    Emerge (new_ident_for env ck_x, reconstruct_clauses clause_list)
  | Estruct field_val_list ->
    let field_val_list = reconstruct_clauses field_val_list in
    Estruct field_val_list
  | Eiterator (it, app, se, partial_w_list, w_list, rst) ->
    let total_w_list = reconstruct_extvalues env (partial_w_list @ w_list) children in
    let partial_w_list, w_list = split_at (List.length partial_w_list) total_w_list in
    Eiterator (it, app, se, partial_w_list, w_list, optional (new_ident_for env) rst)

and reconstruct_extvalues (tenv, cenv) w_list children =
  let consume w (children, result_w_list) =
    if extvalue_compare w dummy_extvalue = 0
    then (List.tl children, reconstruct_class_ref (tenv, cenv) (List.hd children) :: result_w_list)
    else (children, w :: result_w_list) in
  let (children, w_list) = List.fold_right consume w_list (children, []) in
  assert (children = []); (* There should be no more children than dummy_exps! *)
  w_list

and reconstruct_class_ref (tenv, cenv) cr = match cr with
  | Cr_input w -> w
  | Cr_plain w ->
    let er = PatMap.find (Evarpat w) tenv in
    mk_extvalue ~ty:er.er_head.e_ty (Wvar (ident_for_class cenv er.er_class))

and reconstruct_clock env ck = match ck_repr ck with
  | Con (ck, c, x) -> Con (reconstruct_clock env ck, c, new_ident_for env x)
  | _ -> ck

and reconstruct_clock_type env ct = match ct with
  | Cprod ct_list -> Cprod (List.map (reconstruct_clock_type env) ct_list)
  | Ck ck -> Ck (reconstruct_clock env ck)

and new_ident_for ((tenv : tom_env), (cenv : eq_repr list IntMap.t)) x =
  let class_id = (PatMap.find (Evarpat x) tenv).er_class in
  ident_for_class cenv class_id

and ident_for_class =
  let ht = Hashtbl.create 100 in
  fun (cenv : eq_repr list IntMap.t) class_id ->
    try Hashtbl.find ht class_id
    with Not_found ->
      let id =
        let repr_list = IntMap.find class_id cenv
        and make_ident { er_pattern = pat; } =
          Misc.fold_right_1 concat_idents (ident_list_of_pat pat) in
        Misc.fold_right_1 concat_idents (List.map make_ident repr_list) in
      Hashtbl.add ht class_id id;
      id

and pattern_name_for_id ((tenv, cenv) as env) ty id = pattern_name env ty (ident_for_class cenv id)

and pattern_name env ty name = match ty with
  | Tprod ty_list ->
    let component_name i ty =
      pattern_name env ty (concat_idents (gen_var (symbol_for_int i)) name) in
    Etuplepat (mapi component_name ty_list)
  | _ -> Evarpat name

(********************************************************************)
(* Top-level functions: plug everything together to minimize a node *)
(********************************************************************)

let rec fix_local_var_dec ((tenv, cenv) as env) vd (seen, vd_list) =
  let class_id = (PatMap.find (Evarpat vd.v_ident) tenv).er_class in
  if IntSet.mem class_id seen then (seen, vd_list)
  else
    (IntSet.add class_id seen,
     { vd with
       v_ident = new_ident_for env vd.v_ident;
       v_clock = reconstruct_clock env vd.v_clock; } :: vd_list)

and fix_local_var_decs tenv vd_list =
  snd (List.fold_right (fix_local_var_dec tenv) vd_list (IntSet.empty, []))

let rec fix_output_var_dec ((tenv, cenv) as env) vd vd_list =
  let class_id = (PatMap.find (Evarpat vd.v_ident) tenv).er_class in
  { vd with
    v_ident = new_ident_for env vd.v_ident;
    v_clock = reconstruct_clock env vd.v_clock; } :: vd_list

and fix_output_var_decs tenv vd_list = List.fold_right (fix_output_var_dec tenv) vd_list []

let node nd =
  Idents.enter_node nd.n_name;

  (* Initial environment *)
  let tenv =
    let is_input id = List.exists (fun vd -> ident_compare vd.v_ident id = 0) nd.n_input in
    List.fold_left (add_equation is_input) PatMap.empty nd.n_equs in

  (* Compute fix-point of [compute_new_class] *)
  let tenv = separate_classes tenv in

  (* Regroup equivalence classes *)
  let cenv = compute_classes tenv in

  (* Reconstruct equation list from grouped equivalence classes *)
  let eq_list = reconstruct (tenv, cenv) in

  let local = fix_local_var_decs (tenv, cenv) nd.n_local in
  let output = fix_output_var_decs (tenv, cenv) nd.n_output in

  { nd with n_equs = eq_list; n_output = output; n_local = local; }

let program_desc pd pd_list = match pd with
  | Pnode nd -> Pnode (node nd) :: pd_list
  | _ -> pd :: pd_list

let program p = { p with p_desc = List.fold_right program_desc p.p_desc []; }
