(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)

(* Translation from Minils to Obc. *)
open Misc
open Names
open Idents
open Signature
open Obc
open Obc_utils
open Obc_mapfold
open Types
open Clocks
open Initial


let build_anon, find_anon =
  let anon_nodes = ref QualEnv.empty in
  let build_anon nodes =
    let build env nd = match nd with
      | Minils.Pnode nd ->
          if Itfusion.is_anon_node nd.Minils.n_name
          then QualEnv.add nd.Minils.n_name nd env
          else env
      | _ -> env
    in
    anon_nodes := List.fold_left build QualEnv.empty nodes
  in
  let find_anon qn = QualEnv.find qn !anon_nodes in
  build_anon, find_anon

let var_from_name map x =
  begin try
    Env.find x map
  with
      _ ->
        Format.eprintf
          "Internal compiler error: unknown identifier %a@."
          Global_printer.print_ident x;
        assert false
  end

let ext_value_exp_from_name map x = exp_of_pattern (var_from_name map x)

(* let lvar_from_name map ty x = mk_pattern ty (Lvar (var_from_name map x)) *)

let fresh_it () =
  let id = Idents.gen_var "mls2obc" "i" in
  id, mk_var_dec id Initial.tint

let gen_obj_ident n = Idents.gen_var "mls2obc" ((shortname n) ^ "_inst")
let fresh_for = fresh_for "mls2obc"
(*let copy_array = copy_array "mls2obc"*)

let op_from_string op = { qual = Pervasives; name = op; }

let pattern_of_idx_list p l =
  let rec aux p l = match Modules.unalias_type p.pat_ty, l with
    | _, [] -> p
    | Tarray (ty',_), idx :: l -> aux (mk_pattern ty' (Larray (p, idx))) l
    | _ -> internal_error "mls2obc"
  in
  aux p l

let rec exp_of_idx_list e l = match Modules.unalias_type e.w_ty, l with
  | _, [] -> e
  | Tarray (ty',_), idx :: l ->
    exp_of_idx_list (mk_ext_value ty' (Warray (e, idx))) l
  | _ -> internal_error "mls2obc exp_of_idx_list"

let rec extvalue_of_idx_list w l = match Modules.unalias_type w.w_ty, l with
  | _, [] -> w
  | Tarray (ty',_), idx :: l ->
    extvalue_of_idx_list (mk_ext_value ty' (Warray (w, idx))) l
  | _ -> internal_error "mls2obc extvalue_of_idx_list"

let ext_value_of_trunc_idx_list p l =
  let mk_between idx se =
    mk_exp_int (Eop (mk_pervasives "between", [idx; mk_ext_value_exp se.se_ty (Wconst se)]))
  in
  let rec aux p l = match Modules.unalias_type p.w_ty, l with
    | _, [] -> p
    | Tarray (ty', se), idx :: l -> aux (mk_ext_value ty' (Warray (p, mk_between idx se))) l
    | _ -> internal_error "mls2obc ext_value_of_trunc_idx_list"
  in
  aux p l

let rec ty_of_idx_list ty idx_list = match ty, idx_list with
  | _, [] -> ty
  | Tarray(ty, _), _idx::idx_list -> ty_of_idx_list ty idx_list
  | _, _ -> internal_error "mls2obc ty_of_idx_list"

let mk_static_array_power ty c params = match params with
  | [] -> mk_ext_value_exp ty (Wconst c)
  | _ ->
    let se = mk_static_exp ty (Sarray_power (c, params)) in
    mk_ext_value_exp ty (Wconst se)

let array_elt_of_exp idx e =
  match e.e_desc, Modules.unalias_type e.e_ty with
  | Eextvalue { w_desc = Wconst { se_desc = Sarray_power (c, _::new_params) }; }, Tarray (ty,_) ->
     mk_static_array_power ty c new_params
  | _, Tarray (ty,_) ->
      mk_ext_value_exp ty (Warray(ext_value_of_exp e, idx))
  | _ -> internal_error "mls2obc array_elt_of_exp"

let array_elt_of_exp_list idx_list e =
  match e.e_desc, Modules.unalias_type e.e_ty with
    | Eextvalue { w_desc = Wconst { se_desc = Sarray_power (c, params) } }, Tarray (ty,n) ->
      let new_params, _ = Misc.split_at (List.length params - List.length idx_list) params in
      let ty = ty_of_idx_list (Tarray(ty,n)) idx_list in
      mk_static_array_power ty c new_params
    | _ , t ->
        let rec ty id_l t = match id_l, Modules.unalias_type t with
          | [] , t -> t
          | _::id_l , Tarray (t,_) -> ty id_l t
          | _, _ -> internal_error "mls2obc ty"
        in
        mk_exp (ty idx_list t) (Eextvalue (extvalue_of_idx_list (ext_value_of_exp e) idx_list))


(** Creates the expression that checks that the indices
    in idx_list are in the bounds. If idx_list=[e1;..;ep]
    and bounds = [n1;..;np], it returns
    0<= e1 < n1 && .. && 0 <= ep < np *)
let rec bound_check_expr idx_list bounds =
  let mk_comp idx n =
        let e1 = mk_exp_bool (Eop (op_from_string "<",
                                 [idx; mk_ext_value_exp_int (Wconst n)])) in
        let e2 = mk_exp_bool (Eop (op_from_string "<=",
                                 [mk_ext_value_exp_int (Wconst (mk_static_int 0)); idx])) in
          mk_exp_bool (Eop (op_from_string "&", [e1;e2]))
  in
  match (idx_list, bounds) with
    | [idx], n::_ -> mk_comp idx n
    | (idx :: idx_list, n :: bounds) ->
        let e = mk_comp idx n in
          mk_exp_bool (Eop (op_from_string "&",
                           [e; bound_check_expr idx_list bounds]))
    | (_, _) -> internal_error "mls2obc"

let mk_plus_one e = match e.e_desc with
  | Eextvalue ({ w_desc = Wconst idx } as w) ->
      let idx_plus_one = mk_static_int_op (mk_pervasives "+") [idx; mk_static_int 1] in
        { e with e_desc = Eextvalue { w with w_desc = Wconst idx_plus_one; }; }
  | _ ->
      let idx_plus_one = Eop (mk_pervasives "+", [e; mk_exp_const_int 1]) in
        { e with e_desc = idx_plus_one }

(** Creates the action list that copies [src] to [dest],
    updating the value at index [idx_list] with the value [v]. *)
let rec ssa_update_array dest src idx_list v = match Modules.unalias_type dest.pat_ty, idx_list with
  | Tarray (t, n), idx::idx_list ->
      (*Body of the copy loops*)
      let copy i =
        let src_i = array_elt_of_exp i src in
        let dest_i = mk_pattern t (Larray (dest, i)) in
        [Aassgn(dest_i, src_i)]
      in
      (*Copy values < idx*)
      let a_lower = fresh_for (mk_exp_const_int 0) idx copy in
      (* Update the correct element*)
      let src_idx = array_elt_of_exp idx src in
      let dest_idx = mk_pattern t (Larray (dest, idx)) in
      let a_update = ssa_update_array dest_idx src_idx idx_list v in
      (*Copy values > idx*)
      let idx_plus_one = mk_plus_one idx in
      let a_upper = fresh_for idx_plus_one (mk_exp_static_int n) copy in
      [a_lower] @ a_update @ [a_upper]
  | _, _ ->
      [Aassgn(dest, v)]

(** Creates the action list that copies [src] to [dest],
    updating the value of field [f] with the value [v]. *)
let ssa_update_record dest src f v =
  let assgn_act { f_name = l; f_type = ty } =
    let dest_l = mk_pattern ty (Lfield(dest, l)) in
    let src_l = mk_ext_value_exp ty (Wfield(src, l)) in
    if f = l then
      Aassgn(dest_l, v)
    else
      Aassgn(dest_l, src_l)
  in
  let fields = match dest.pat_ty with
    | Tid n -> Modules.find_struct n
    | _ -> Misc.internal_error "mls2obc field of nonstruct"
  in
  List.map assgn_act fields

let rec control map ck s = match ck with
  | Clocks.Cbase | Cvar { contents = Cindex _ } -> s
  | Cvar { contents = Clink ck } -> control map ck s
  | Clocks.Con(ck, c, n)  ->
    let x = ext_value_exp_from_name map n in
    control map ck (Acase(x, [(c, mk_block [s])]))

let reinit o =
  Acall ([], o, Mreset, [])

let rec translate_pat map ty pat = match pat, ty with
  | Minils.Evarpat x, _ -> [ var_from_name map x ]
  | Minils.Etuplepat pat_list, Tprod ty_l  ->
      List.fold_right2 (fun ty pat acc -> (translate_pat map ty pat) @ acc)
        ty_l pat_list []
  | Minils.Etuplepat _, _ -> Misc.internal_error "Ill-typed pattern"

let translate_var_dec l =
  let one_var { Minils.v_ident = x; Minils.v_type = t; Minils.v_linearity = lin; v_loc = loc } =
    mk_var_dec ~loc:loc ~linearity:lin x t
  in
  List.rev (List.rev_map one_var l)

let rec translate_extvalue map w = match w.Minils.w_desc with
  | Minils.Wvar x -> ext_value_of_pattern (var_from_name map x)
  | _ ->
    let desc = match w.Minils.w_desc with
      | Minils.Wconst v -> Wconst v
      | Minils.Wvar _ -> assert false
      | Minils.Wfield (w1, f) -> Wfield (translate_extvalue map w1, f)
      | Minils.Wwhen (w1, _, _) | Minils.Wreinit(_, w1)  -> (translate_extvalue map w1).w_desc
    in
    mk_ext_value w.Minils.w_ty desc

and translate_extvalue_to_exp map w =
  mk_exp ~loc:w.Minils.w_loc w.Minils.w_ty (Eextvalue (translate_extvalue map w))

(* [translate e = c] *)
let rec translate map e =
  let desc = match e.Minils.e_desc with
    | Minils.Eextvalue w ->
        let w = translate_extvalue map w in Eextvalue w
    | Minils.Eapp ({ Minils.a_op = Minils.Eequal }, w_list, _) ->
      Eop (op_from_string "=", List.map (translate_extvalue_to_exp map) w_list)
    | Minils.Eapp ({ Minils.a_op = Minils.Efun n }, e_list, _)
        when Mls_utils.is_op n ->
        Eop (n, List.map (translate_extvalue_to_exp map ) e_list)
    | Minils.Estruct f_e_list ->
        let type_name = (match e.Minils.e_ty with
                           | Tid name -> name
                           | _ -> assert false) in
        let f_e_list = List.map
          (fun (f, e) -> (f, (translate_extvalue_to_exp map e))) f_e_list in
          Estruct (type_name, f_e_list)
  (*Remaining array operators*)
    | Minils.Eapp ({ Minils.a_op = Minils.Earray }, e_list, _) ->
        Earray (List.map (translate_extvalue_to_exp map ) e_list)
    | Minils.Eapp ({ Minils.a_op = Minils.Eselect;
                     Minils.a_params = idx_list }, e_list, _) ->
        let e = translate_extvalue map (assert_1 e_list) in
        let idx_list = List.map mk_exp_static_int idx_list in
        Eextvalue (extvalue_of_idx_list e idx_list)
    | Minils.Ewhen(e,_,_) ->
        let e = translate map e in
        e.e_desc
  (* Already treated cases when translating the [eq] *)
    | Minils.Eiterator _ | Minils.Emerge _ | Minils.Efby _
    | Minils.Eapp ({Minils.a_op=(Minils.Enode _|Minils.Efun _|Minils.Econcat
                                |Minils.Eupdate|Minils.Eselect_dyn
                                |Minils.Eselect_trunc|Minils.Eselect_slice
                                |Minils.Earray_fill|Minils.Efield_update
                                |Minils.Eifthenelse)}, _, _) ->
        internal_error "mls2obc"
  in
    mk_exp e.Minils.e_ty desc

and translate_act_extvalue map pat w =
  match pat with
    | Minils.Evarpat n ->
        [Aassgn (var_from_name map n, translate_extvalue_to_exp map w)]
    | _ -> assert false

(* [translate pat act = si, d] *)
and translate_act map pat
    ({ Minils.e_desc = desc } as act) =
    match pat, desc with
   (* When Merge *)
    | pat, Minils.Ewhen (e,_,_) -> translate_act map pat e
    | Minils.Evarpat x, Minils.Emerge (y, c_act_list) ->
        let x = var_from_name map x in
        let translate_c_extvalue (c, w) =
          c, mk_block [Aassgn (x, translate_extvalue_to_exp map w)]
        in

        [Acase (ext_value_exp_from_name map y,
                List.map translate_c_extvalue c_act_list)]
   (* Array ops *)
    | Minils.Evarpat x,
        Minils.Eapp ({ Minils.a_op = Minils.Econcat }, [e1; e2], _) ->
        let cpt1, cpt1d = fresh_it () in
        let cpt2, cpt2d = fresh_it () in
        let x = var_from_name map x in
        let _t = x.pat_ty in
        (match e1.Minils.w_ty, e2.Minils.w_ty with
           | Tarray (t1, n1), Tarray (t2, n2) ->
               let e1 = translate_extvalue_to_exp map e1 in
               let e2 = translate_extvalue_to_exp map e2 in
               let a1 =
                 Afor (cpt1d, mk_exp_const_int 0, mk_exp_static_int n1,
                      mk_block [Aassgn (mk_pattern t1 (Larray (x, mk_evar_int cpt1)),
                                       array_elt_of_exp (mk_evar_int cpt1) e1)] ) in
               let idx = mk_exp_int (Eop (op_from_string "+",
                                         [ mk_exp_static_int n1; mk_evar_int cpt2])) in
               let p2 = array_elt_of_exp (mk_evar_int cpt2) e2 in
               let a2 = Afor (cpt2d, mk_exp_const_int 0, mk_exp_static_int n2,
                             mk_block [Aassgn (mk_pattern t2 (Larray (x, idx)), p2)] )
               in
               [a1; a2]
           | _ -> assert false)

    | Minils.Evarpat x,
          Minils.Eapp ({ Minils.a_op = Minils.Earray_fill; Minils.a_params = n_list }, [e], _) ->
        let e = translate_extvalue_to_exp map e in
        let x = var_from_name map x in
        let t = match x.pat_ty with
          | Tarray (t,_) -> t
          | _ -> Misc.internal_error "mls2obc select slice type"
        in

        let rec make_loop power_list replace = match power_list with
          | [] -> x, replace
          | p :: power_list ->
            let cpt, cptd = fresh_it () in
            let e, replace =
              make_loop power_list
                        (fun y -> [Afor (cptd, mk_exp_const_int 0,
                                         mk_exp_static_int p, mk_block (replace y))]) in
            let e = Larray (e, mk_evar_int cpt) in
            (mk_pattern t e, replace)
        in
        let e, b = make_loop n_list (fun y -> [Aassgn (y, e)]) in
        b e

    | Minils.Evarpat x,
            Minils.Eapp ({ Minils.a_op = Minils.Eselect_slice;
                           Minils.a_params = [idx1; idx2] }, [e], _) ->
        let cpt, cptd = fresh_it () in
        let e = translate_extvalue_to_exp map e in
        let x = var_from_name map x in
        let t = match x.pat_ty with
          | Tarray (t,_) -> t
          | _ -> Misc.internal_error "mls2obc select slice type"
        in
        let idx = mk_exp_int (Eop (op_from_string "+",
                                  [mk_evar_int cpt; mk_exp_static_int idx1 ])) in
        (* bound = (idx2 - idx1) + 1*)
        let bound = mk_static_int_op (op_from_string "+")
          [ mk_static_int 1; mk_static_int_op (op_from_string "-") [idx2;idx1] ] in
         [ Afor (cptd, mk_exp_const_int 0, mk_exp_static_int bound,
                mk_block [Aassgn (mk_pattern t (Larray (x, mk_evar_int cpt)),
                                  array_elt_of_exp idx e)] ) ]

    | Minils.Evarpat x, Minils.Eapp ({ Minils.a_op = Minils.Eselect_dyn }, e1::e2::idx, _) ->
        let x = var_from_name map x in
        let bounds = Mls_utils.bounds_list e1.Minils.w_ty in
        let e1 = translate_extvalue map e1 in
        let idx = List.map (translate_extvalue_to_exp map) idx in
        let w = extvalue_of_idx_list e1 idx in
        let true_act = Aassgn (x, mk_exp w.w_ty (Eextvalue w)) in
        let false_act = Aassgn (x, translate_extvalue_to_exp map e2) in
        let cond = bound_check_expr idx bounds in
          [ mk_ifthenelse cond [true_act] [false_act] ]

    | Minils.Evarpat x, Minils.Eapp ({ Minils.a_op = Minils.Eselect_trunc }, e1::idx, _) ->
        let x = var_from_name map x in
        let _bounds = Mls_utils.bounds_list e1.Minils.w_ty in
        let e1 = translate_extvalue map e1 in
        let idx = List.map (translate_extvalue_to_exp map) idx in
        let w = ext_value_of_trunc_idx_list e1 idx in
        [Aassgn (x, mk_exp w.w_ty (Eextvalue w))]

    | Minils.Evarpat x, Minils.Eapp ({ Minils.a_op = Minils.Eupdate }, e1::e2::idx, _) ->
        let x = var_from_name map x in
        let bounds = Mls_utils.bounds_list e1.Minils.w_ty in
        let idx = List.map (translate_extvalue_to_exp map) idx in
        let e1 = translate_extvalue_to_exp map e1 in
        let e2 = translate_extvalue_to_exp map e2 in
        let cond = bound_check_expr idx bounds in
        let copy = Aassgn (x, e1) in
        if !Compiler_options.strict_ssa
        then (
          let ssa_up = ssa_update_array x e1 idx e2 in
          [ mk_ifthenelse cond ssa_up [copy] ]
        ) else (
          let assgn = Aassgn (pattern_of_idx_list x idx, e2) in
          [copy; mk_if cond [assgn]]
        )

    | Minils.Evarpat x,
      Minils.Eapp ({ Minils.a_op = Minils.Efield_update;
                     Minils.a_params = [{ se_desc = Sfield f }] }, [e1; e2], _) ->
        let x = var_from_name map x in
        let e1' = translate_extvalue map e1 in
        let e2 = translate_extvalue_to_exp map e2 in
        if !Compiler_options.strict_ssa
        then ssa_update_record x e1' f e2
        else (
          let copy = Aassgn (x, translate_extvalue_to_exp map e1) in
          let action = Aassgn (mk_pattern (Types.Tid (Modules.find_field f)) (Lfield (x, f)), e2) in
          [copy; action]
        )
    | Minils.Evarpat n, _ ->
        [Aassgn (var_from_name map n, translate map act)]
    | _ ->
      Format.eprintf "%a The pattern %a should be a simple var to be translated to obc.@."
        Location.print_location act.Minils.e_loc Mls_printer.print_pat pat;
      assert false

(** In an iteration, objects used are element of object arrays *)
type obj_array = { oa_index : Obc.pattern list; oa_size : static_exp list }

(** A [None] context is normal, otherwise, we are in an iteration *)
type call_context = obj_array option

let mk_obj_call_from_context c n = match c with
  | None -> Oobj n
  | Some oa -> Oarray (n, oa.oa_index)

let size_from_call_context c = match c with
  | None -> None
  | Some oa -> Some (oa.oa_size)

let empty_call_context = None

(** [si] the initialization actions used in the reset method,
    [j] obj decs
    [s] the actions used in the step method.
    [v] var decs *)
let rec translate_eq map call_context
    (v, si, j, s)
    ({ Minils.eq_lhs = pat; Minils.eq_base_ck = ck; Minils.eq_rhs = e } as eq) =
  let { Minils.e_desc = desc; Minils.e_loc = loc } = e in
  match (pat, desc) with
    | _pat, Minils.Ewhen (e,_,_) ->
        translate_eq map call_context (v, si, j, s) {eq with Minils.eq_rhs = e}
    (* TODO Efby and Eifthenelse should be dealt with in translate_act, no ? *)
    | Minils.Evarpat n, Minils.Efby (opt_c, e) ->
        let x = var_from_name map n in
        let si = (match opt_c with
                    | None -> si
                    | Some c -> (Aassgn (x, mk_ext_value_exp_static x.pat_ty c)) :: si) in
        let action = Aassgn (var_from_name map n, translate_extvalue_to_exp map e) in
        v, si, j, (control map ck action) :: s
(* should be unnecessary
    | Minils.Etuplepat p_list,
        Minils.Eapp({ Minils.a_op = Minils.Etuple }, act_list, _) ->
        List.fold_right2
          (fun pat e ->
             translate_eq map call_context
               (Minils.mk_equation pat e))
          p_list act_list (v, si, j, s)
*)
    | pat, Minils.Eapp({ Minils.a_op = Minils.Eifthenelse }, [e1;e2;e3], _) ->
        let cond = translate_extvalue_to_exp map e1 in
        let true_act = translate_act_extvalue map pat e2 in
        let false_act = translate_act_extvalue map pat e3 in
        let action = mk_ifthenelse cond true_act false_act in
        v, si, j, (control map ck action) :: s

    | _pat, Minils.Eapp({ Minils.a_op =
        Minils.Efun ({ qual = Module "Iostream"; name = "printf" | "fprintf" } as q)},
                       args, _) ->
      let action = Aop (q, List.map (translate_extvalue_to_exp map) args) in
      v, si, j, (control map ck action) :: s

    | pat, Minils.Eapp ({ Minils.a_op = Minils.Efun _ | Minils.Enode _ } as app, e_list, r) ->
        let name_list = translate_pat map e.Minils.e_ty pat in
        let c_list = List.map (translate_extvalue_to_exp map) e_list in
        let v', si', j', action = mk_node_call map call_context
          app loc name_list c_list e.Minils.e_ty in
        let action = List.map (control map ck) action in
        let s = (match r, app.Minils.a_op with
                   | Some r, Minils.Enode _ ->
                       let ck = Clocks.Con (ck, Initial.ptrue, r) in
                       let ra = List.map (control map ck) si' in
                       ra @ action @ s
                   | _, _ -> action @ s) in
        v' @ v, si'@si, j'@j, s

    | pat, Minils.Eiterator (it, app, n_list, pe_list, e_list, reset) ->
        let name_list = translate_pat map e.Minils.e_ty pat in
        let p_list = List.map (translate_extvalue_to_exp map) pe_list in
        let c_list = List.map (translate_extvalue_to_exp map) e_list in
        let xl, xdl = List.split (List.map (fun _ -> fresh_it ()) n_list) in
        let call_context =
          Some { oa_index = List.map (fun x -> mk_pattern_int (Lvar x)) xl;
                 oa_size = n_list} in
        let n_list = List.map mk_exp_static_int n_list in
        let si', j', action = translate_iterator map call_context it
          name_list app loc n_list xl xdl p_list c_list e.Minils.e_ty in
        let action = List.map (control map ck) action in
        let s =
          (match reset, app.Minils.a_op with
             | Some r, Minils.Enode _ ->
                 let ck = Clocks.Con (ck, Initial.ptrue, r) in
                 let ra = List.map (control map ck) si' in
                   ra @ action @ s
             | _, _ -> action @ s)
        in (v, si' @ si, j' @ j, s)

    | (pat, _) ->
        let action = translate_act map pat e in
        let action = List.map (control map ck) action in
          v, si, j, action @ s

and translate_eq_list map call_context act_list =
  let rev_act = List.rev act_list in
  List.fold_left (translate_eq map call_context) ([], [], [], []) rev_act

and mk_node_call map call_context app loc (name_list : Obc.pattern list) args ty =
  match app.Minils.a_op with
    | Minils.Efun f when Mls_utils.is_op f ->
        let act = match name_list with
          | [] -> Aop (f, args)
          | [name] ->
              let e = mk_exp ty (Eop(f, args)) in
              Aassgn (name, e)
          | _ ->
            Misc.unsupported "mls2obc: external function with multiple return values" in
        [], [], [], [act]

    | Minils.Enode f when Itfusion.is_anon_node f ->
        let add_input env vd =
          Env.add vd.Minils.v_ident
            (mk_pattern vd.Minils.v_type (Lvar vd.Minils.v_ident)) env in
        let build env vd a = Env.add vd.Minils.v_ident a env in
        let subst_act_list env act_list =
          let exp funs env e = match e.e_desc with
            | Eextvalue { w_desc = Wvar x } ->
                let e =
                  (try Env.find x env
                  with Not_found -> e) in
                  e, env
            | _ -> Obc_mapfold.exp funs env e
          in
          let funs = { Obc_mapfold.defaults with exp = exp } in
          let act_list, _ = mapfold (Obc_mapfold.act_it funs) env act_list in
            act_list
        in

        let nd = find_anon f in
        let map = List.fold_left add_input map nd.Minils.n_input in
        let map = List.fold_left2 build map nd.Minils.n_output name_list in
        let map = List.fold_left add_input map nd.Minils.n_local in
        let v, si, j, s = translate_eq_list map call_context nd.Minils.n_equs in
        let env = List.fold_left2 build Env.empty nd.Minils.n_input args in
          v @ nd.Minils.n_local, si, j, subst_act_list env s

    | Minils.Enode f | Minils.Efun f ->
        let id = match app.Minils.a_id with
          | None -> gen_obj_ident f
          | Some id -> id
        in
        let o = mk_obj_call_from_context call_context id in
        let obj =
          { o_ident = obj_ref_name o; o_class = f;
            o_params = app.Minils.a_params;
            o_size = size_from_call_context call_context; o_loc = loc } in
        let si = match app.Minils.a_op with
          | Minils.Efun _ -> []
          | Minils.Enode _ -> [reinit o]
          | _ -> assert false
        in
        let s = [Acall (name_list, o, Mstep, args)] in
        [], si, [obj], s
    | _ -> assert false

and translate_iterator map call_context it name_list
    app loc n_list xl xdl p_list c_list ty =
  let rec unarray n ty = match ty, n with
    | Tarray (t,_), 1 -> t
    | Tarray (t,_), n -> unarray (n-1) t
    | _ ->
        Format.eprintf "%a" Global_printer.print_type ty;
        internal_error "mls2obc"
  in
  let unarray = unarray (List.length n_list) in
  let array_of_output name_list ty_list =
    let rec aux l ty xl = match ty, xl with
      | _, [] -> l
      | Tarray(tyn, _), x :: xl -> aux (mk_pattern ~loc:loc tyn (Larray(l, mk_evar_int x))) tyn xl
      | _, _ -> assert false
    in
    List.map2 (fun l ty -> aux l ty xl) name_list ty_list
  in
  let array_of_input c_list =
    List.map (array_elt_of_exp_list (List.map mk_evar_int xl)) c_list
  in
  let mk_loop b xdl nl =
    let rec mk_loop b xdl nl = match xdl, nl with
      | xd::[], n::[] -> Afor (xd, mk_exp_const_int 0, n, b)
      | xd::xdl, n::nl -> mk_loop (mk_block [Afor (xd, mk_exp_const_int 0, n, b)]) xdl nl
      | _, _ -> assert false
    in
    mk_loop b (List.rev xdl) nl
  in
  match it with
    | Minils.Imap ->
        let c_list = array_of_input c_list in
        let ty_list = List.map unarray (Types.unprod ty) in
        let name_list = array_of_output name_list (Types.unprod ty) in
        let node_out_ty = Types.prod ty_list in
        let v, si, j, action = mk_node_call map call_context
          app loc name_list (p_list@c_list) node_out_ty in
        let v = translate_var_dec v in
        let b = mk_block ~locals:v action in
        let bi = mk_block si in
          [mk_loop bi xdl n_list], j, [mk_loop b xdl n_list]

    | Minils.Imapi ->
        let c_list = array_of_input c_list in
        let ty_list = List.map unarray (Types.unprod ty) in
        let name_list = array_of_output name_list (Types.unprod ty) in
        let node_out_ty = Types.prod ty_list in
        let v, si, j, action = mk_node_call map call_context
          app loc name_list (p_list@c_list@(List.map mk_evar_int xl)) node_out_ty in
        let v = translate_var_dec v in
        let b = mk_block ~locals:v action in
        let bi = mk_block si in
          [mk_loop bi xdl n_list], j, [mk_loop b xdl n_list]

    | Minils.Imapfold ->
        let (c_list, acc_in) = split_last c_list in
        let c_list = array_of_input c_list in
        let ty_list = Types.unprod ty in
        let ty_name_list, _ = Misc.split_last ty_list in
        let (name_list, acc_out) = Misc.split_last name_list in
        let name_list = array_of_output name_list ty_name_list in
        let node_out_ty = Types.prod (Misc.map_butlast unarray ty_list) in
        let v, si, j, action = mk_node_call map call_context app loc
          (name_list @ [ acc_out ])
          (p_list @ c_list @ [ exp_of_pattern acc_out ])
          node_out_ty
        in
        let v = translate_var_dec v in
        let b = mk_block ~locals:v action in
        let bi = mk_block si in
          [mk_loop bi xdl n_list], j,
           [Aassgn (acc_out, acc_in); mk_loop b xdl n_list]

    | Minils.Ifold ->
        let (c_list, acc_in) = split_last c_list in
        let c_list = array_of_input c_list in
        let acc_out = last_element name_list in
        let v, si, j, action =
          mk_node_call map call_context app loc name_list
            (p_list @ c_list @ [ exp_of_pattern acc_out ]) ty
        in
        let v = translate_var_dec v in
        let b = mk_block ~locals:v action in
        let bi = mk_block si in
          [mk_loop bi xdl n_list], j,
           [ Aassgn (acc_out, acc_in); mk_loop b xdl n_list]

    | Minils.Ifoldi ->
        let (c_list, acc_in) = split_last c_list in
        let c_list = array_of_input c_list in
        let acc_out = last_element name_list in
        let v, si, j, action = mk_node_call map call_context app loc name_list
          (p_list @ c_list @ (List.map mk_evar_int xl) @ [ exp_of_pattern acc_out ]) ty
        in
        let v = translate_var_dec v in
        let b = mk_block ~locals:v action in
        let bi = mk_block si in
          [mk_loop bi xdl n_list], j,
           [ Aassgn (acc_out, acc_in); mk_loop b xdl n_list]

let remove m d_list =
  List.filter (fun { Minils.v_ident = n } -> not (List.mem_assoc n m)) d_list

let translate_contract map mem_var_tys =
  function
    | None -> ([], [], [], [], [])
    | Some
        {
          Minils.c_eq = eq_list;
          Minils.c_local = d_list;
        } ->
        let (v, si, j, s_list) = translate_eq_list map empty_call_context eq_list in
        let d_list = translate_var_dec (v @ d_list) in
        let m, d_list = List.partition
          (fun vd -> List.exists (fun (i,_) -> i = vd.v_ident) mem_var_tys) d_list in
         (m, si, j, s_list, d_list)

(** Returns a map, mapping variables names to the variables
    where they will be stored. *)
let subst_map inputs outputs controllables c_locals locals mem_tys =
  (* Create a map that simply maps each var to itself *)
  let map =
    List.fold_left
      (fun m { Minils.v_ident = x; Minils.v_type = ty } -> Env.add x (mk_pattern ty (Lvar x)) m)
      Env.empty (inputs @ outputs @ controllables @ c_locals @ locals)
  in
  List.fold_left (fun map (x, x_ty) -> Env.add x (mk_pattern x_ty (Lmem x)) map) map mem_tys

let translate_node
    ({ Minils.n_name = f; Minils.n_input = i_list; Minils.n_output = o_list;
      Minils.n_local = d_list; Minils.n_equs = eq_list; Minils.n_stateful = stateful;
      Minils.n_contract = contract; Minils.n_params = params; Minils.n_loc = loc;
      Minils.n_mem_alloc = mem_alloc
    } as n) =
  Idents.enter_node f;
  let mem_var_tys = Mls_utils.node_memory_vars n in
  let c_list, c_locals =
    match contract with
    | None -> [], []
    | Some c -> c.Minils.c_controllables, c.Minils.c_local in
  let subst_map = subst_map i_list o_list c_list c_locals d_list mem_var_tys in
  let (v, si, j, s_list) = translate_eq_list subst_map empty_call_context eq_list in
  let (m_c, si', j', s_list', d_list') = translate_contract subst_map mem_var_tys contract in
  let i_list = translate_var_dec i_list in
  let o_list = translate_var_dec o_list in
  let d_list = translate_var_dec (List.rev_append v d_list) in
  let m, d_list = List.partition
    (fun vd -> List.exists (fun (i,_) -> i = vd.v_ident) mem_var_tys) d_list in
  let m', o_list =
    List.partition
      (fun vd -> List.exists (fun (i,_) -> i = vd.v_ident) mem_var_tys) o_list in
  let s = List.rev_append (List.rev s_list) s_list' in
  let j = j' @ j in
  let si = si @ si' in
  let stepm = { m_name = Mstep; m_inputs = i_list; m_outputs = o_list;
                m_body = mk_block ~locals:(List.rev_append d_list' d_list) s }
  in
  let resetm = { m_name = Mreset; m_inputs = []; m_outputs = []; m_body = mk_block si } in
  if stateful
  then { cd_name = f; cd_stateful = true; cd_mems = m' @ m @ m_c; cd_params = params;
         cd_objs = j; cd_methods = [stepm; resetm]; cd_loc = loc; cd_mem_alloc = mem_alloc }
  else (
    (* Functions won't have [Mreset] or memories,
       they still have [params] and instances (of functions) *)
    { cd_name = f; cd_stateful = false; cd_mems = []; cd_params = params;
      cd_objs = j; cd_methods = [stepm]; cd_loc = loc; cd_mem_alloc = mem_alloc }
  )

let translate_ty_def { Minils.t_name = name; Minils.t_desc = tdesc;
                       Minils.t_loc = loc } =
  let tdesc = match tdesc with
    | Minils.Type_abs -> Type_abs
    | Minils.Type_alias ln -> Type_alias ln
    | Minils.Type_enum tag_name_list -> Type_enum tag_name_list
    | Minils.Type_struct field_ty_list -> Type_struct field_ty_list
  in
  { t_name = name; t_desc = tdesc; t_loc = loc }

let translate_const_def { Minils.c_name = name; Minils.c_value = se;
                          Minils.c_type = ty; Minils.c_loc = loc } =
  { Obc.c_name = name;
    Obc.c_value = se;
    Obc.c_type = ty;
    Obc.c_loc = loc }

let program { Minils.p_modname = p_modname; Minils.p_opened = p_o; Minils.p_desc = pd; } =
  build_anon pd;

  let program_desc pd acc = match pd with
    | Minils.Pnode n when not (Itfusion.is_anon_node n.Minils.n_name) ->
        Pclass (translate_node n) :: acc
    (* dont't translate anonymous nodes, they will be inlined *)
    | Minils.Pnode _ -> acc
    | Minils.Ptype t -> Ptype (translate_ty_def t) :: acc
    | Minils.Pconst c -> Pconst (translate_const_def c) :: acc
  in
  let p_desc = List.fold_right program_desc pd [] in
  { p_modname = p_modname;
    p_opened = p_o;
    p_desc = p_desc }


let signature s =
  { sig_name = s.Minils.sig_name;
    sig_inputs = s.Minils.sig_inputs;
    sig_stateful = s.Minils.sig_stateful;
    sig_outputs = s.Minils.sig_outputs;
    sig_params = s.Minils.sig_params;
    sig_param_constraints = s.Minils.sig_param_constraints;
    sig_loc = s.Minils.sig_loc }

let interface i =
  let interface_decl id = match id with
    | Minils.Itypedef td -> Itypedef (translate_ty_def td)
    | Minils.Iconstdef cd -> Iconstdef (translate_const_def cd)
    | Minils.Isignature s -> Isignature (signature s)
  in
  { i_modname = i.Minils.i_modname;
    i_opened = i.Minils.i_opened;
    i_desc = List.map interface_decl i.Minils.i_desc }
