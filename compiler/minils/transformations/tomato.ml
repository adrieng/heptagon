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

let debug = false

let debug_do f () = if debug then f () else ()

(*
  Data-flow minimization on MiniLS:

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
        er_clock_type : ct;
        er_pattern : pat;
        er_head : exp;
        er_children : class_ref list;
        er_add_when : exp -> exp;
        er_when_count : int;
      }

  type tom_env = eq_repr PatMap.t

  let class_of_ident tenv id = try Some (PatMap.find (Evarpat id) tenv) with Not_found -> None

  open Mls_printer

  let print_class_ref fmt cr = match cr with
    | Cr_plain id -> print_ident fmt id
    | Cr_input w -> print_extvalue fmt w

  let debug_tenv fmt tenv =
    let debug pat repr =
      Format.fprintf fmt "%a => @[class %d,@ pattern %a,@ head { %a },@ children [%a]@]@."
        print_pat pat
        repr.er_class
        print_pat repr.er_pattern
        print_exp repr.er_head
        (print_list_r print_class_ref "" ";" "") repr.er_children
    in
    PatMap.iter debug tenv
end

open TomEnv

let gen_var = Idents.gen_var ~reset:false "tomato"

let dummy_var = gen_var "dummy"
let dummy_extvalue = mk_extvalue ~ty:Initial.tint (Wvar dummy_var)

let initial_class = 0

let concat_idents id1 id2 = gen_var (Idents.name id1 ^ "_" ^ Idents.name id2)

let symbol_for_int i =
  if i > 25
  then "a" ^ string_of_int i
  else String.make 1 (Char.chr (Char.code 'a' + i))

(*******************************************************************)
(* Comparison modulo equivalence classes                           *)
(*******************************************************************)

module ClockCompareModulo =
struct
  let (env : (int * int list) Env.t ref) = ref Env.empty

  let find_ident id = try Some (Env.find id !env) with Not_found -> None

  let ident_compare_modulo id1 id2 =
    match find_ident id1, find_ident id2 with
    | None, None -> ident_compare id1 id2 (* two inputs *)
    | Some (c1, p1), Some (c2, p2) -> (* two internal variables *)
      let cr = compare c1 c2 in
      if cr <> 0 then cr else list_compare Pervasives.compare p1 p2
    | Some _, None -> -1
    | None, Some _ -> 1

  let rec clock_compare ck1 ck2 = match ck1, ck2 with
    | Cvar { contents = Clink ck1; }, _ -> clock_compare ck1 ck2
    | _, Cvar { contents = Clink ck2; } -> clock_compare ck1 ck2
    | Cbase, Cbase -> 0
    | Cvar lr1, Cvar lr2 -> link_compare_modulo !lr1 !lr2
    | Con (ck1, cn1, vi1), Con (ck2, cn2, vi2) ->
      let cr1 = compare cn1 cn2 in
      if cr1 <> 0 then cr1 else
        let cr2 = ident_compare_modulo vi1 vi2 in
        if cr2 <> 0 then cr2 else clock_compare ck1 ck2
    | Cbase , _ -> 1

    | Cvar _, Cbase -> -1
    | Cvar _, _ -> 1

    | Con _, _ -> -1

  and link_compare_modulo li1 li2 = match li1, li2 with
    | Cindex _, Cindex _ -> 0
    | Clink ck1, Clink ck2 -> clock_compare ck1 ck2
    | Cindex _, _ -> 1
    | Clink _, _ -> -1

  and clock_type_compare ct1 ct2 = match ct1, ct2 with
    | Ck ck1, Ck ck2 -> clock_compare ck1 ck2
    | Cprod ct_list1, Cprod ct_list2 -> list_compare clock_type_compare ct_list1 ct_list2
    | Ck _, Cprod _ -> 1
    | Cprod _, Ck _ -> -1

end

module CompareModulo = Mls_compare.Make(ClockCompareModulo)

(*******************************************************************)
(* Construct an initial minimization environment                   *)
(*******************************************************************)

let class_ref_of_var is_input w x = if is_input x then Cr_input w else Cr_plain x

let rec add_equation is_input (tenv : tom_env) eq =
  let add_clause (cn, w) class_id_list =
    let class_id_list, w = extvalue is_input w class_id_list in
    class_id_list, (cn, w) in

  let id x = x in

  let ed, add_when, when_count, class_id_list =
    let rec decompose e = match e.e_desc with
      | Eextvalue w ->
        let class_id_list, w = extvalue is_input w [] in
        Eextvalue w, id, 0, class_id_list

      | Eapp (app, w_list, rst) ->
        let class_id_list, w_list = mapfold_right (extvalue is_input) w_list [] in
        let class_id_list = match rst with
          | None -> class_id_list
          | Some rst ->
            class_ref_of_var is_input
              (mk_extvalue ~ty:Initial.tbool ~linearity:Linearity.Ltop (Wvar rst)) rst
            :: class_id_list
        in
        Eapp (app, w_list, optional (fun _ -> dummy_var) rst), id, 0, class_id_list

      | Efby (seo, w) ->
        let class_id_list, w = extvalue is_input w [] in
        Efby (seo, w), id, 0, class_id_list

      | Ewhen (e', cn, x) ->
        let ed, add_when, when_count, class_id_list = decompose e' in
        ed, (fun e' -> { e with e_desc = Ewhen (add_when e', cn, x) }), when_count + 1,
        class_ref_of_var is_input
          (mk_extvalue ~clock:e'.e_base_ck ~ty:Initial.tbool
                       ~linearity:Linearity.Ltop (Wvar x)) x
        :: class_id_list

      | Emerge (x, clause_list) ->
        let class_id_list, clause_list = mapfold_right add_clause clause_list [] in
        let x_id =
          class_ref_of_var is_input
            (mk_extvalue ~clock:e.e_base_ck ~ty:Initial.tbool
                         ~linearity:Linearity.Ltop (Wvar x)) x
        in
        Emerge (dummy_var, clause_list), id, 0, x_id :: class_id_list

      | Eiterator (it, app, sel, partial_w_list, w_list, rst) ->
        let class_id_list, partial_w_list = mapfold_right (extvalue is_input) partial_w_list [] in
        let class_id_list, w_list = mapfold_right (extvalue is_input) w_list class_id_list in
        let class_id_list = match rst with
          | None -> class_id_list
          | Some rst ->
            class_ref_of_var is_input
              (mk_extvalue ~ty:Initial.tbool ~linearity:Linearity.Ltop (Wvar rst)) rst
            :: class_id_list
        in
        Eiterator (it, app, sel, partial_w_list, w_list, optional (fun _ -> dummy_var) rst),
        id, 0, class_id_list

      | Estruct field_val_list ->
        let class_id_list, field_val_list = mapfold_right add_clause field_val_list [] in
        Estruct field_val_list, id, 0, class_id_list
    in
    decompose eq.eq_rhs
  in

  let eq_repr =
    {
      er_class = initial_class;
      er_pattern = eq.eq_lhs;
      er_head = { eq.eq_rhs with e_desc = ed; };
      er_children = class_id_list;
      er_add_when = add_when;
      er_when_count = when_count;
      er_clock_type = eq.eq_rhs.e_ct;
    }
  in

  PatMap.add eq.eq_lhs eq_repr tenv

and extvalue is_input w class_id_list =
  let rec decompose w class_id_list =
    let class_id_list, wd = match w.w_desc with
      | Wconst _ -> class_id_list, w.w_desc
      | Wvar x -> class_ref_of_var is_input w x :: class_id_list, Wvar dummy_var
      | Wfield (w, f) ->
        let class_id_list, w = decompose w class_id_list in
        class_id_list, Wfield (w, f)
      | Wwhen (w, cn, x) ->
        (* Create the extvalue representing x *)
        let w_x = mk_extvalue ~ty:Initial.tbool ~clock:w.w_ck ~linearity:w.w_linearity (Wvar x) in
        let class_id_list, w = decompose w (class_ref_of_var is_input w_x x :: class_id_list) in
        class_id_list, Wwhen (w, cn, dummy_var)
    in
    class_id_list, { w with w_desc = wd; }
  in
  decompose w class_id_list

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

type info = Info of var_ident

let new_name mapping x =
  try
    let Info x' = Env.find x mapping in
    x'
  with Not_found -> x

(* Takes a tomato env and returns a renaming environment *)
let construct_mapping (tenv, cenv) =
  let construct_mapping_eq_repr _ eq_repr_list mapping =
    let rec ty_list_of_ty ty acc = match ty with
        | Tprod ty_list -> List.fold_right ty_list_of_ty ty_list acc
        | _ -> ty :: acc
    in

    let rec ck_list_of_ct ct acc = match ct with
      | Cprod ct_list -> List.fold_right ck_list_of_ct ct_list acc
      | Ck ck -> ck :: acc
    in

    let idents_list =
      (* In OCaml, constructors ain't no functions :'( *)
      let add l1 l2 = l1 :: l2 in
      List.fold_right
        (List.map2 add)
        (List.map (fun er -> ident_list_of_pat er.er_pattern) eq_repr_list)
        (* Ugly, rewrite *)
        (Misc.repeat_list [] (List.length (ident_list_of_pat (List.hd eq_repr_list).er_pattern)))
    in

    let first = List.hd eq_repr_list in
    let ty_list = ty_list_of_ty first.er_head.e_ty [] in
    let ck_list = ck_list_of_ct first.er_clock_type [] in

    let fused_ident_list = List.map (Misc.fold_right_1 concat_idents) idents_list in

    Misc.fold_left4
      (fun mapping x_list fused_x ty ck ->
        List.fold_left
          (fun mapping x ->
            Env.add x (Info fused_x) mapping)
          mapping x_list)
      mapping
      idents_list
      fused_ident_list
      ty_list
      ck_list
  in

  IntMap.fold construct_mapping_eq_repr cenv Env.empty

let rec reconstruct ((tenv, cenv) as env) mapping =

  let reconstruct_class id eq_repr_list eq_list =
    assert (List.length eq_repr_list > 0);

    let repr = List.hd eq_repr_list in

    let e =
      let children =
        Misc.take (List.length repr.er_children - repr.er_when_count) repr.er_children in

      let ed = reconstruct_exp_desc mapping repr.er_head.e_desc repr.er_children in
      let ck = reconstruct_clock mapping repr.er_head.e_base_ck in
      let level_ck =
        reconstruct_clock mapping repr.er_head.e_level_ck in (* not strictly needed, done for
                                                            consistency reasons *)
      let ct = reconstruct_clock_type mapping repr.er_head.e_ct in
      { repr.er_head with e_desc = ed; e_base_ck = ck; e_level_ck = level_ck; e_ct = ct; } in

    let e = repr.er_add_when e in

    let pat = reconstruct_pattern mapping repr.er_pattern in

    mk_equation pat e :: eq_list in
  IntMap.fold reconstruct_class cenv []

and reconstruct_exp_desc mapping headd children =
  let reconstruct_clauses clause_list children =
    let (qn_list, w_list) = List.split clause_list in
    let w_list = reconstruct_extvalues mapping w_list children in
    List.combine qn_list w_list in

  match headd with

  | Eextvalue w ->
    let w = assert_1 (reconstruct_extvalues mapping [w] children) in
    Eextvalue w

  | Efby (ini, w) ->
    let w = assert_1 (reconstruct_extvalues mapping [w] children) in
    Efby (ini, w)

  | Eapp (app, w_list, rst_dummy) ->
    let rst, children = match rst_dummy with
      | None -> None, children
      | Some _ -> Some (reconstruct_class_ref mapping (List.hd children)), List.tl children in
    Eapp (app, reconstruct_extvalues mapping w_list children, rst)

  | Ewhen _ -> assert false (* no Ewhen in exprs *)

  | Emerge (x_ref, clause_list) ->
    let x_ref, children = List.hd children, List.tl children in
    Emerge (reconstruct_class_ref mapping x_ref,
            reconstruct_clauses clause_list children)

  | Estruct field_val_list ->
    let field_val_list = reconstruct_clauses field_val_list children in
    Estruct field_val_list

  | Eiterator (it, app, sel, partial_w_list, w_list, rst_dummy) ->
    let rst, children = match rst_dummy with
      | None -> None, children
      | Some _ -> Some (reconstruct_class_ref mapping (List.hd children)), List.tl children in
    let total_w_list = reconstruct_extvalues mapping (w_list @ partial_w_list) children in
    let w_list, partial_w_list = split_at (List.length w_list) total_w_list in
    Eiterator (it, app, sel, partial_w_list, w_list, rst)

and reconstruct_extvalues mapping w_list children =
  let rec reconstruct_extvalue w (children : class_ref list) = match w.w_desc with
    | Wconst _ -> w, children
    | Wvar _ ->
      let w = { w with w_desc = Wvar (reconstruct_class_ref mapping (List.hd children)); } in
      w, List.tl children
    | Wwhen (w', cn, _) ->
      let w_x = reconstruct_class_ref mapping (List.hd children) in
      let w', children = reconstruct_extvalue w' (List.tl children) in
      { w with w_desc = Wwhen (w', cn, w_x) }, children
    | Wfield (w', fn) ->
      let w', children = reconstruct_extvalue w' children in
      { w with w_desc = Wfield (w', fn); }, children
  in

  let consume w (children, result_w_list) =
    let w, children = reconstruct_extvalue w children in
    let w = { w with w_ck = reconstruct_clock mapping w.w_ck } in
    children, w :: result_w_list
  in

  let (children, w_list) = List.fold_right consume w_list (List.rev children, []) in
  w_list

(* and extract_name w = match w.w_desc with *)
(*   | Wvar x -> x *)
(*   | _ -> invalid_arg "extract_name: not a var" *)

and reconstruct_class_ref mapping cr = match cr with
  | Cr_input w -> (match w.w_desc with Wvar x -> x | _ -> assert false)
  | Cr_plain x ->
    let Info x = Env.find x mapping in
    x

and reconstruct_clock mapping ck = match ck_repr ck with
  | Con (ck, c, x) -> Con (reconstruct_clock mapping ck, c, new_name mapping x)
  | _ -> ck

and reconstruct_clock_type mapping ct = match ct with
  | Cprod ct_list -> Cprod (List.map (reconstruct_clock_type mapping) ct_list)
  | Ck ck -> Ck (reconstruct_clock mapping ck)

and reconstruct_pattern mapping pat = match pat with
  | Evarpat x -> Evarpat (new_name mapping x)
  | Etuplepat pat_list -> Etuplepat (List.map (reconstruct_pattern mapping) pat_list)


(***********************************************************************)
(* Compute the next equivalence classes for a minimization environment *)
(***********************************************************************)

module EqClasses = Map.Make(
  struct
    type t = exp * ct * (int * int list) option list

    let unsafe { e_desc = ed } = match ed with
      | Eapp (app, _, _) | Eiterator (_, app, _, _, _, _) -> app.a_unsafe
      | _ -> false

    let compare (e1, ck1, cr_list1) (e2, ck2, cr_list2) =
      let cr = ClockCompareModulo.clock_type_compare ck1 ck2 in
      if cr <> 0 then cr
      else
        (let cr = CompareModulo.exp_compare e1 e2 in
         if cr <> 0 then cr
         else
           if unsafe e1 then 1
           else
             (if unsafe e2 then -1 else list_compare Pervasives.compare cr_list1 cr_list2))
  end)

let rec path_environment tenv =
  let enrich_env pat { er_class = id } env =
    let rec enrich pat path env = match pat with
      | Evarpat x -> Env.add x (id, path) env
      | Etuplepat pat_list ->
        let (_, env) =
          List.fold_right
            (fun pat (i, env) -> (i + 1, enrich pat (i :: path) env))
            pat_list
            (0, env)
        in
        env
    in
    enrich pat [] env
  in
  PatMap.fold enrich_env tenv Env.empty;;

let compute_new_class (tenv : tom_env) =
  let mapping = path_environment tenv in

  (* Do comparisons with respect to tenv! *)
  ClockCompareModulo.env := mapping;

  let fresh_id, get_id = let id = ref 0 in ((fun () -> incr id; !id), (fun () -> !id)) in

  let add_eq_repr _ eqr classes =
    let map_class_ref cref = match cref with
      | Cr_input _ -> None
      | Cr_plain x -> Some (Env.find x mapping)
    in
    let children = List.map map_class_ref eqr.er_children in

    let key = (eqr.er_head, eqr.er_clock_type, children) in
    let id = try EqClasses.find key classes with Not_found -> fresh_id () in

    eqr.er_class <- id;
    EqClasses.add key id classes

  in

  let classes = PatMap.fold add_eq_repr tenv EqClasses.empty in

  (get_id (), tenv)

let rec separate_classes tenv =
  let rec fix (id, tenv) =
    let new_id, tenv = compute_new_class tenv in
    debug_do (fun () -> Format.printf "New tenv %d:\n%a@." id debug_tenv tenv) ();
    if new_id = id then tenv else fix (new_id, tenv)
  in
  debug_do (fun () -> Format.printf "Initial tenv:\n%a@." debug_tenv tenv) ();
  let id, tenv = compute_new_class tenv in
  debug_do (fun () -> Format.printf "New tenv %d:\n%a@." id debug_tenv tenv) ();
  fix (id, tenv)

(********************************************************************)
(* Top-level functions: plug everything together to minimize a node *)
(********************************************************************)

let rec fix_local_var_dec mapping vd (seen, vd_list) =
  let Info x = Env.find vd.v_ident mapping in
  if IdentSet.mem x seen
  then (seen, vd_list)
  else
    (IdentSet.add x seen,
     { vd with v_ident = x; v_clock = reconstruct_clock mapping vd.v_clock; } :: vd_list)

and fix_local_var_decs mapping vd_list =
  snd (List.fold_right (fix_local_var_dec mapping) vd_list (IdentSet.empty, []))

(* May add new local equations in the case of fused outputs *)
let rec fix_output_var_dec mapping vd (seen, equs, vd_list) =
  let Info x = Env.find vd.v_ident mapping in
  if IdentSet.mem x seen
  then
    let new_id = vd.v_ident in
    let new_clock = reconstruct_clock mapping vd.v_clock in
    let new_vd = { vd with v_ident = new_id; v_clock = new_clock } in
    let new_eq =
      let w = mk_extvalue ~ty:vd.v_type ~clock:new_clock ~linearity:Linearity.Ltop (Wvar x) in
      mk_equation
        (Evarpat new_id)
        (mk_exp new_clock vd.v_type ~ct:(Ck new_clock)
           ~ck:new_clock ~linearity:Linearity.Ltop (Eextvalue w))
    in
    (seen, new_eq :: equs, new_vd :: vd_list)
  else
    (IdentSet.add x seen, equs,
     { vd with v_ident = x; v_clock = reconstruct_clock mapping vd.v_clock } :: vd_list)

and fix_output_var_decs tenv (equs, vd_list) =
  let (_, eq_list, vd_list) =
    List.fold_right (fix_output_var_dec tenv) vd_list (IdentSet.empty, equs, []) in
  eq_list, vd_list

let update_node nd =
  let change_name vd arg = { arg with a_name = Some (name vd.v_ident) } in
  let sign = Modules.find_value nd.n_name in
  let sign = { sign with node_outputs = List.map2 change_name nd.n_output sign.node_outputs } in
  Signature.check_signature sign;
  ignore (Modules.replace_value nd.n_name sign)

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

  (* Map old identifiers to new ones *)
  let mapping = construct_mapping (tenv, cenv) in

  (* Reconstruct equation list from grouped equivalence classes *)
  let eq_list = reconstruct (tenv, cenv) mapping in

  (* Fix renamed var_decs, and add intermediate equations for fused outputs *)
  let local = fix_local_var_decs mapping nd.n_local in
  let eq_list, output = fix_output_var_decs mapping (eq_list, nd.n_output) in

  let nd = { nd with n_equs = eq_list; n_output = output; n_local = local; } in
  update_node nd;
  nd

let program_desc pd pd_list = match pd with
  | Pnode nd -> Pnode (node nd) :: pd_list
  | _ -> pd :: pd_list

let program p = { p with p_desc = List.fold_right program_desc p.p_desc []; }
