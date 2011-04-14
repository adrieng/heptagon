(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* Translation from Minils to Obc. *)
open Misc
open Names
open Idents
open Signature
open Obc
open Obc_utils
open Obc_mapfold
open Types
open Static
open Initial


let fresh_it () =
  let id = Idents.gen_var "mls2obc" "i" in
  id, mk_var_dec id Initial.tint

let gen_obj_ident n = Idents.gen_var "mls2obc" ((shortname n) ^ "_inst")

let op_from_string op = { qual = Pervasives; name = op; }

let rec pattern_of_idx_list p l =
  let rec aux p l = match p.pat_ty, l with
    | _, [] -> p
    | Tarray (ty',_), idx :: l -> aux (mk_pattern ty' (Larray (p, idx))) l
    | _ -> internal_error "mls2obc" 1
  in
  aux p l

let rec pattern_of_trunc_idx_list p l =
  let mk_between idx se =
    mk_exp_int (Eop (mk_pervasives "between", [idx; mk_exp se.se_ty (Econst se)]))
  in
  let rec aux p l = match p.pat_ty, l with
    | _, [] -> p
    | Tarray (ty', se), idx :: l -> aux (mk_pattern ty' (Larray (p, mk_between idx se))) l
    | _ -> internal_error "mls2obc" 1
  in
  aux p l

let array_elt_of_exp idx e =
  match e.e_desc, Modules.unalias_type e.e_ty with
    | Econst ({ se_desc = Sarray_power (c, _) }), Tarray (ty,_) ->
        mk_exp ty (Econst c)
    | _, Tarray (ty,_) ->
        mk_pattern_exp ty (Larray(pattern_of_exp e, mk_exp Initial.tint (Epattern idx)))
    | _ -> internal_error "mls2obc" 2

(** Creates the expression that checks that the indices
    in idx_list are in the bounds. If idx_list=[e1;..;ep]
    and bounds = [n1;..;np], it returns
    0<= e1 < n1 && .. && 0 <= ep < np *)
let rec bound_check_expr idx_list bounds =
  let mk_comp idx n =
        let e1 = mk_exp_bool (Eop (op_from_string "<",
                                 [idx; mk_exp_int (Econst n)])) in
        let e2 = mk_exp_bool (Eop (op_from_string "<=",
                                 [mk_exp_int (Econst (Sint 0)); idx])) in
          mk_exp_bool (Eop (op_from_string "&", [e1;e2]))
  in
  match (idx_list, bounds) with
    | [idx], [n] -> mk_comp idx n
    | (idx :: idx_list, n :: bounds) ->
        let e = mk_comp idx n in
          mk_exp_bool (Eop (op_from_string "&",
                           [e; bound_check_expr idx_list bounds]))
    | (_, _) -> internal_error "mls2obc" 3

let reinit o =
  Acall ([], o, Mreset, [])

let rec translate_pat map = function
  | Minils.Evarpat x -> [ Control.var_from_name map x ]
  | Minils.Etuplepat pat_list ->
      List.fold_right (fun pat acc -> (translate_pat map pat) @ acc)
        pat_list []

let translate_var_dec l =
  let one_var { Minils.v_ident = x; Minils.v_type = t; v_loc = loc } =
    mk_var_dec ~loc:loc x t
  in
  List.map one_var l

let rec translate_extvalue map w =
  let desc = match w.w_desc with
  | Wconst v -> Econst v
  | Wvar x -> Epattern (Control.var_from_name map n)
  | Wfield (w1, f) ->
      let w1 = translate_extvalue map (assert_1 e_list) in
        Epattern (mk_pattern e.e_ty (Lfield (pattern_of_exp e, f)))
  | Wwhen (w1, c, x) ->
      let e1 = translate_extvalue map w1 in
        e1.e_desc
  in
    mk_exp e.Minils.e_ty desc

(* [translate e = c] *)
let rec translate map e =
  let desc = match e.Minils.e_desc with
    | Minils.Eextvalue w ->
        let e = translate_ext_value map e in e.e_desc
    | Minils.Eapp ({ Minils.a_op = Minils.Eequal }, e_list, _) ->
        Eop (op_from_string "=", List.map (translate_extvalue map ) e_list)
    | Minils.Eapp ({ Minils.a_op = Minils.Efun n }, e_list, _)
        when Mls_utils.is_op n ->
        Eop (n, List.map (translate_extvalue map ) e_list)
    | Minils.Estruct f_e_list ->
        let type_name = (match e.Minils.e_ty with
                           | Tid name -> name
                           | _ -> assert false) in
        let f_e_list = List.map
          (fun (f, e) -> (f, (translate_extvalue map e))) f_e_list in
          Estruct (type_name, f_e_list)
  (*Remaining array operators*)
    | Minils.Eapp ({ Minils.a_op = Minils.Earray }, e_list, _) ->
        Earray (List.map (translate_extvalue map ) e_list)
    | Minils.Eapp ({ Minils.a_op = Minils.Eselect;
                     Minils.a_params = idx }, e_list, _) ->
        let e = translate_extvalue map (assert_1 e_list) in
        let idx_list = List.map (fun idx -> mk_exp tint (Econst idx)) idx in
          Epattern (pattern_of_idx_list (pattern_of_exp e) idx_list)
  (* Already treated cases when translating the [eq] *)
    | Minils.Eiterator _ | Minils.Emerge _ | Minils.Efby _
    | Minils.Eapp ({Minils.a_op=(Minils.Enode _|Minils.Efun _|Minils.Econcat
                                 |Minils.Eupdate|Minils.Eselect_dyn
                                 |Minils.Eselect_trunc|Minils.Eselect_slice
                                 |Minils.Earray_fill|Minils.Efield_update
                                 |Minils.Eifthenelse|Minils.Etuple)}, _, _) ->
        internal_error "mls2obc" 5
  in
    mk_exp e.Minils.e_ty desc

(* [translate pat act = si, d] *)
and translate_act map pat
    ({ Minils.e_desc = desc } as act) =
    match pat, desc with
    | Minils.Etuplepat p_list,
        Minils.Eapp ({ Minils.a_op = Minils.Etuple }, act_list, _) ->
        List.flatten (List.map2 (translate_act map) p_list act_list)
    | Minils.Etuplepat p_list, Minils.Econst { se_desc = Stuple se_list } ->
        let const_list = Mls_utils.exp_list_of_static_exp_list se_list in
        List.flatten (List.map2 (translate_act map) p_list const_list)
   (* When Merge *)
    | pat, Minils.Emerge (x, c_act_list) ->
        let pattern = Control.var_from_name map x in
        [Acase (mk_exp pattern.pat_ty (Epattern pattern),
               translate_c_act_list map pat c_act_list)]
   (* Array ops *)
    | Minils.Evarpat x,
        Minils.Eapp ({ Minils.a_op = Minils.Econcat }, [e1; e2], _) ->
        let cpt1, cpt1d = fresh_it () in
        let cpt2, cpt2d = fresh_it () in
        let x = Control.var_from_name map x in
        let t = x.pat_ty in
        (match e1.Minils.e_ty, e2.Minils.e_ty with
           | Tarray (t1, n1), Tarray (t2, n2) ->
               let e1 = translate_extvalue map e1 in
               let e2 = translate_extvalue map e2 in
               let a1 =
                 Afor (cpt1d, mk_static_int 0, n1,
                      mk_block [Aassgn (mk_pattern t1 (Larray (x, mk_evar_int cpt1)),
                                       mk_pattern_exp t1 (Larray (pattern_of_exp e1,
                                                                 mk_evar_int cpt1)))] ) in
               let idx = mk_exp_int (Eop (op_from_string "+",
                                         [ mk_exp_int (Econst n1); mk_evar_int cpt2])) in
               let p2 = mk_pattern_exp t2 (Larray (pattern_of_exp e2, mk_evar_int cpt2)) in
               let a2 = Afor (cpt2d, mk_static_int 0, n2,
                             mk_block [Aassgn (mk_pattern t2 (Larray (x, idx)), p2)] )
               in
               [a1; a2]
           | _ -> assert false)

    | Minils.Evarpat x,
          Minils.Eapp ({ Minils.a_op = Minils.Earray_fill; Minils.a_params = [n] }, [e], _) ->
        let cpt, cptd = fresh_it () in
        let e = translate_extvalue map e in
        let x = Control.var_from_name map x in
        let t = match x.pat_ty with
          | Tarray (t,_) -> t
          | _ -> Misc.internal_error "mls2obc select slice type" 5
        in
        let b =  mk_block [Aassgn (mk_pattern t (Larray (x, mk_evar_int cpt)), e) ] in
          [ Afor (cptd, mk_static_int 0, n, b) ]

    | Minils.Evarpat x,
            Minils.Eapp ({ Minils.a_op = Minils.Eselect_slice;
                           Minils.a_params = [idx1; idx2] }, [e], _) ->
        let cpt, cptd = fresh_it () in
        let e = translate_extvalue map e in
        let x = Control.var_from_name map x in
        let t = match x.pat_ty with
          | Tarray (t,_) -> t
          | _ -> Misc.internal_error "mls2obc select slice type" 5
        in
        let idx = mk_exp_int (Eop (op_from_string "+",
                                  [mk_evar_int cpt; mk_exp_int (Econst idx1) ])) in
        (* bound = (idx2 - idx1) + 1*)
        let bound = mk_static_int_op (op_from_string "+")
          [ mk_static_int 1; mk_static_int_op (op_from_string "-") [idx2;idx1] ] in
         [ Afor (cptd, mk_static_int 0, bound,
                mk_block [Aassgn (mk_pattern t (Larray (x, mk_evar_int cpt)),
                                  mk_pattern_exp t (Larray (pattern_of_exp e, idx)))] ) ]

    | Minils.Evarpat x, Minils.Eapp ({ Minils.a_op = Minils.Eselect_dyn }, e1::e2::idx, _) ->
        let x = Control.var_from_name map x in
        let bounds = Mls_utils.bounds_list e1.Minils.e_ty in
        let e1 = translate_extvalue map e1 in
        let idx = List.map (translate_extvalue map) idx in
        let p = pattern_of_idx_list (pattern_of_exp e1) idx in
        let true_act = Aassgn (x, mk_exp p.pat_ty (Epattern p)) in
        let false_act = Aassgn (x, translate_extvalue map e2) in
        let cond = bound_check_expr idx bounds in
          [ Acase (cond, [ ptrue, mk_block [true_act]; pfalse, mk_block [false_act] ]) ]

    | Minils.Evarpat x, Minils.Eapp ({ Minils.a_op = Minils.Eselect_trunc }, e1::idx, _) ->
        let x = Control.var_from_name map x in
        let bounds = Mls_utils.bounds_list e1.Minils.e_ty in
        let e1 = translate_extvalue map e1 in
        let idx = List.map (translate_extvalue map) idx in
        let p = pattern_of_trunc_idx_list (pattern_of_exp e1) idx in
          [Aassgn (x, mk_exp p.pat_ty (Epattern p))]

    | Minils.Evarpat x, Minils.Eapp ({ Minils.a_op = Minils.Eupdate }, e1::e2::idx, _) ->
        let x = Control.var_from_name map x in
     (** TODO: remplacer par if 0 < e && e < n then for () ; o[e] = v; for () else o = a *)
        let bounds = Mls_utils.bounds_list e1.Minils.e_ty in
        let idx = List.map (translate_extvalue map) idx in
        let action = Aassgn (pattern_of_idx_list x idx,
                            translate_extvalue map e2) in
        let cond = bound_check_expr idx bounds in
        let action = Acase (cond, [ ptrue, mk_block [action] ]) in
        let copy = Aassgn (x, translate_extvalue map e1) in
          [copy; action]

    (** TODO: remplacer par o = { f = v; g = a.g; h = a.h; ... } *)
    | Minils.Evarpat x,
      Minils.Eapp ({ Minils.a_op = Minils.Efield_update;
                     Minils.a_params = [{ se_desc = Sfield f }] }, [e1; e2], _) ->
        let x = Control.var_from_name map x in
        let copy = Aassgn (x, translate_extvalue map e1) in
        let action = Aassgn (mk_pattern x.pat_ty (Lfield (x, f)),
                            translate_extvalue map e2) in (* TODO wrong type *)
        [copy; action]

    | Minils.Evarpat n, _ ->
        [Aassgn (Control.var_from_name map n, translate map act)]
    | _ ->
      Format.eprintf "%a The pattern %a should be a simple var to be translated to obc.@."
        Location.print_location act.Minils.e_loc Mls_printer.print_pat pat;
      assert false

and translate_c_act_list map pat c_act_list =
  List.map
    (fun (c, act) -> (c, mk_block (translate_act map pat act)))
    c_act_list

(** In an iteration, objects used are element of object arrays *)
type obj_array = { oa_index : Obc.pattern; oa_size : static_exp }

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
let rec translate_eq map call_context { Minils.eq_lhs = pat; Minils.eq_rhs = e }
    (v, si, j, s) =
  let { Minils.e_desc = desc; Minils.e_ck = ck; Minils.e_loc = loc } = e in
  match (pat, desc) with
    | Minils.Evarpat n, Minils.Efby (opt_c, e) ->
        let x = Control.var_from_name map n in
        let si = (match opt_c with
                    | None -> si
                    | Some c -> (Aassgn (x, mk_exp x.pat_ty (Econst c))) :: si) in
        let action = Aassgn (Control.var_from_name map n, translate_extvalue map e) in
        v, si, j, (Control.control map ck action) :: s
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
        let cond = translate_extvalue map e1 in
        let vt, si, j, true_act = translate_act map pat e2 in
        let vf, si, j, false_act = translate_act map pat e3 in
        let vf = translate_var_dec vf in
        let vt = translate_var_dec vt in
        let action =
          Acase (cond, [ptrue, mk_block ~locals:vt true_act;
                        pfalse, mk_block ~locals:vf false_act]) in
          v, si, j, (Control.control map ck action) :: s

    | pat, Minils.Eapp ({ Minils.a_op = Minils.Efun _ | Minils.Enode _ } as app, e_list, r) ->
        let name_list = translate_pat map pat in
        let c_list = List.map (translate_extvalue map) e_list in
        let v', si', j', action = mk_node_call map call_context
          app loc name_list c_list e.Minils.e_ty in
        let action = List.map (Control.control map ck) action in
        let s = (match r, app.Minils.a_op with
                   | Some r, Minils.Enode _ ->
                       let ck = Clocks.Con (ck, Initial.ptrue, r) in
                       let ra = List.map (Control.control map ck) si' in
                       ra @ action @ s
                   | _, _ -> action @ s) in
        v' @ v, si'@si, j'@j, s

    | pat, Minils.Eiterator (it, app, n, pe_list, e_list, reset) ->
        let name_list = translate_pat map pat in
        let p_list = List.map (translate_extvalue map) pe_list in
        let c_list = List.map (translate_extvalue map) e_list in
        let x, xd = fresh_it () in
        let call_context =
          Some { oa_index = mk_pattern_int (Lvar x); oa_size = n} in
        let si', j', action = translate_iterator map call_context it
          name_list app loc n x xd p_list c_list e.Minils.e_ty in
        let action = List.map (Control.control map ck) action in
        let s =
          (match reset, app.Minils.a_op with
             | Some r, Minils.Enode _ ->
                 let ck = Clocks.Con (ck, Initial.ptrue, r) in
                 let ra = List.map (Control.control map ck) si' in
                   ra @ action @ s
             | _, _ -> action @ s)
        in (v, si' @ si, j' @ j, s)

    | (pat, _) ->
        let action = translate_act map pat e in
        let action = List.map (Control.control map ck) action in
          v, si, j, action @ s

and translate_eq_list map call_context act_list =
  List.fold_right (translate_eq map call_context) act_list ([], [], [], [])

and mk_node_call map call_context app loc name_list args ty =
  match app.Minils.a_op with
    | Minils.Efun f when Mls_utils.is_op f ->
        let e = mk_exp ty (Eop(f, args)) in
        [], [], [], [Aassgn(List.hd name_list, e)]

    | Minils.Enode f when Itfusion.is_anon_node f ->
        let add_input env vd = Env.add vd.Minils.v_ident
          (mk_pattern vd.Minils.v_type (Lvar vd.Minils.v_ident)) env in
        let build env vd a = Env.add vd.Minils.v_ident a env in
        let subst_act_list env act_list =
          let exp funs env e = match e.e_desc with
            | Epattern { pat_desc = Lvar x } ->
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

        let nd = Itfusion.find_anon_node f in
        let map = List.fold_left add_input map nd.Minils.n_input in
        let map = List.fold_left2 build map nd.Minils.n_output name_list in
        let map = List.fold_left add_input map nd.Minils.n_local in
        let v, si, j, s = translate_eq_list map call_context nd.Minils.n_equs in
        let env = List.fold_left2 build Env.empty nd.Minils.n_input args in
          v @ nd.Minils.n_local, si, j, subst_act_list env s

    | Minils.Enode f | Minils.Efun f ->
        let o = mk_obj_call_from_context call_context (gen_obj_ident f) in
        let obj =
          { o_ident = obj_ref_name o; o_class = f;
            o_params = app.Minils.a_params;
            o_size = size_from_call_context call_context; o_loc = loc } in
        let si = (match app.Minils.a_op with
                   | Minils.Efun _ -> []
                   | Minils.Enode _ -> [reinit o]
                   | _ -> assert false) in
        let s = [Acall (name_list, o, Mstep, args)] in
        [], si, [obj], s
    | _ -> assert false

and translate_iterator map call_context it name_list
    app loc n x xd p_list c_list ty =
  let unarray ty = match ty with
    | Tarray (t,_) -> t
    | _ ->
        Format.eprintf "%a" Global_printer.print_type ty;
        internal_error "mls2obc" 6
  in
  let array_of_output name_list ty_list =
    List.map2 (fun l ty -> mk_pattern ty (Larray (l, mk_evar_int x))) name_list ty_list
  in
  let array_of_input c_list =
    List.map (array_elt_of_exp (mk_pattern_int (Lvar x))) c_list in
  match it with
    | Minils.Imap ->
        let c_list = array_of_input c_list in
        let ty_list = List.map unarray (Types.unprod ty) in
        let name_list = array_of_output name_list ty_list in
        let node_out_ty = Types.prod ty_list in
        let v, si, j, action = mk_node_call map call_context
          app loc name_list (p_list@c_list) node_out_ty in
        let v = translate_var_dec v in
        let b = mk_block ~locals:v action in
        let bi = mk_block si in
          [Afor (xd, mk_static_int 0, n, bi)], j,
           [Afor (xd, mk_static_int 0, n, b)]

    | Minils.Imapi ->
        let c_list = array_of_input c_list in
        let ty_list = List.map unarray (Types.unprod ty) in
        let name_list = array_of_output name_list ty_list in
        let node_out_ty = Types.prod ty_list in
        let v, si, j, action = mk_node_call map call_context
          app loc name_list (p_list@c_list@[mk_evar_int x]) node_out_ty in
        let v = translate_var_dec v in
        let b = mk_block ~locals:v action in
        let bi = mk_block si in
          [Afor (xd, mk_static_int 0, n, bi)], j,
           [Afor (xd, mk_static_int 0, n, b)]

    | Minils.Imapfold ->
        let (c_list, acc_in) = split_last c_list in
        let c_list = array_of_input c_list in
        let ty_list = Misc.map_butlast unarray (Types.unprod ty) in
        let ty_name_list, ty_acc_out = Misc.split_last ty_list in
        let (name_list, acc_out) = Misc.split_last name_list in
        let name_list = array_of_output name_list ty_name_list in
        let node_out_ty = Types.prod ty_list in
        let v, si, j, action = mk_node_call map call_context app loc
          (name_list @ [ acc_out ])
          (p_list @ c_list @ [ mk_exp acc_out.pat_ty (Epattern acc_out) ])
          node_out_ty
        in
        let v = translate_var_dec v in
        let b = mk_block ~locals:v action in
        let bi = mk_block si in
          [Afor (xd, mk_static_int 0, n, bi)], j,
           [Aassgn (acc_out, acc_in); Afor (xd, mk_static_int 0, n, b)]

    | Minils.Ifold ->
        let (c_list, acc_in) = split_last c_list in
        let c_list = array_of_input c_list in
        let acc_out = last_element name_list in
        let v, si, j, action =
          mk_node_call map call_context app loc name_list
            (p_list @ c_list @ [ mk_exp acc_out.pat_ty (Epattern acc_out) ]) ty
        in
        let v = translate_var_dec v in
        let b = mk_block ~locals:v action in
        let bi = mk_block si in
          [Afor (xd, mk_static_int 0, n, bi)], j,
           [ Aassgn (acc_out, acc_in); Afor (xd, mk_static_int 0, n, b) ]

    | Minils.Ifoldi ->
        let (c_list, acc_in) = split_last c_list in
        let c_list = array_of_input c_list in
        let acc_out = last_element name_list in
        let v, si, j, action = mk_node_call map call_context app loc name_list
          (p_list @ c_list @ [ mk_evar_int x;
                               mk_exp acc_out.pat_ty (Epattern acc_out) ]) ty
        in
        let v = translate_var_dec v in
        let b = mk_block ~locals:v action in
        let bi = mk_block si in
          [Afor (xd, mk_static_int 0, n, bi)], j,
           [ Aassgn (acc_out, acc_in); Afor (xd, mk_static_int 0, n, b) ]

let remove m d_list =
  List.filter (fun { Minils.v_ident = n } -> not (List.mem_assoc n m)) d_list

let translate_contract map mem_var_tys =
  function
    | None -> ([], [], [], [])
    | Some
        {
          Minils.c_eq = eq_list;
          Minils.c_local = d_list;
        } ->
        let (v, si, j, s_list) = translate_eq_list map empty_call_context eq_list in
        let d_list = translate_var_dec (v @ d_list) in
        let d_list = List.filter
          (fun vd -> not (List.exists (fun (i,_) -> i = vd.v_ident) mem_var_tys)) d_list in
         (si, j, s_list, d_list)

(** Returns a map, mapping variables names to the variables
    where they will be stored. *)
let subst_map inputs outputs locals mem_tys =
  (* Create a map that simply maps each var to itself *)
  let map =
    List.fold_left
      (fun m { Minils.v_ident = x; Minils.v_type = ty } -> Env.add x (mk_pattern ty (Lvar x)) m)
      Env.empty (inputs @ outputs @ locals)
  in
  List.fold_left (fun map (x, x_ty) -> Env.add x (mk_pattern x_ty (Lmem x)) map) map mem_tys

let translate_node
    ({ Minils.n_name = f; Minils.n_input = i_list; Minils.n_output = o_list;
      Minils.n_local = d_list; Minils.n_equs = eq_list; Minils.n_stateful = stateful;
      Minils.n_contract = contract; Minils.n_params = params; Minils.n_loc = loc;
    } as n) =
  Idents.enter_node f;
  let mem_var_tys = Mls_utils.node_memory_vars n in
  let subst_map = subst_map i_list o_list d_list mem_var_tys in
  let (v, si, j, s_list) = translate_eq_list subst_map empty_call_context eq_list in
  let (si', j', s_list', d_list') = translate_contract subst_map mem_var_tys contract in
  let i_list = translate_var_dec i_list in
  let o_list = translate_var_dec o_list in
  let d_list = translate_var_dec (v @ d_list) in
  let m, d_list = List.partition
    (fun vd -> List.exists (fun (i,_) -> i = vd.v_ident) mem_var_tys) d_list in
  let s = Control.joinlist (s_list @ s_list') in
  let j = j' @ j in
  let si = Control.joinlist (si @ si') in
  let stepm = { m_name = Mstep; m_inputs = i_list; m_outputs = o_list;
                m_body = mk_block ~locals:(d_list' @ d_list) s }
  in
  let resetm = { m_name = Mreset; m_inputs = []; m_outputs = []; m_body = mk_block si } in
  if stateful
  then { cd_name = f; cd_stateful = true; cd_mems = m; cd_params = params;
         cd_objs = j; cd_methods = [stepm; resetm]; cd_loc = loc; }
  else (
    (* Functions won't have [Mreset] or memories,
       they still have [params] and instances (of functions) *)
    { cd_name = f; cd_stateful = false; cd_mems = []; cd_params = params;
      cd_objs = j; cd_methods = [stepm]; cd_loc = loc; }
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
  { c_name = name;
    c_value = se;
    c_type = ty;
    c_loc = loc }

let program { Minils.p_modname = p_modname; Minils.p_opened = p_module_list;
              Minils.p_types = p_type_list;
              Minils.p_nodes = p_node_list; Minils.p_consts = p_const_list } =
  { p_modname = p_modname;
    p_opened = p_module_list;
    p_types = List.map translate_ty_def p_type_list;
    p_consts = List.map translate_const_def p_const_list;
    p_classes = List.map translate_node p_node_list; }


