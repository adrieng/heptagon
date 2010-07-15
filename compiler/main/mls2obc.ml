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
open Ident
open Signature
open Obc
open Types
open Control
open Static

let gen_obj_name n =
  (shortname n) ^ "_mem" ^ (gen_symbol ())

let op_from_string op = Modname { qual = "Pervasives"; id = op; }

let rec lhs_of_idx_list e = function
  | [] -> e | idx :: l -> mk_lhs (Larray (lhs_of_idx_list e l, idx))

let array_elt_of_exp idx e =
  match e.e_desc with
    | Econst ({ se_desc = Sarray_power (c, _) }) ->
        mk_exp (Econst c)
    | _ ->
        mk_lhs_exp (Larray(lhs_of_exp e, mk_exp (Elhs idx)))

(** Creates the expression that checks that the indices
    in idx_list are in the bounds. If idx_list=[e1;..;ep]
    and bounds = [n1;..;np], it returns
    e1 <= n1 && .. && ep <= np *)
let rec bound_check_expr idx_list bounds =
  match (idx_list, bounds) with
    | [idx], [n] ->
        mk_exp (Eop (op_from_string "<",
                     [ idx; mk_exp (Econst n)]))
    | (idx :: idx_list, n :: bounds) ->
        let e = mk_exp (Eop (op_from_string "<",
                             [idx; mk_exp (Econst n)])) in
          mk_exp (Eop (op_from_string "&",
                       [e; bound_check_expr idx_list bounds]))
    | (_, _) -> assert false

let reinit o =
  Acall ([], o, Mreset, [])

let rec translate_pat map = function
  | Minils.Evarpat x -> [ var_from_name map x ]
  | Minils.Etuplepat pat_list ->
      List.fold_right (fun pat acc -> (translate_pat map pat) @ acc)
        pat_list []

(* [translate e = c] *)
let rec translate map (m, si, j, s) e =
  let desc = match e.Minils.e_desc with
    | Minils.Econst v -> Econst v
    | Minils.Evar n -> Elhs (var_from_name map n)
    | Minils.Eapp ({ Minils.a_op = Minils.Efun n },
                   e_list, _) when Mls_utils.is_op n ->
        Eop (n, List.map (translate map (m, si, j, s)) e_list)
    | Minils.Ewhen (e, _, _) ->
        let e = translate map (m, si, j, s) e in
          e.e_desc
    | Minils.Estruct f_e_list ->
        let type_name =
          (match e.Minils.e_ty with
             | Tid name -> name
             | _ -> assert false) in
        let f_e_list =
          List.map
            (fun (f, e) -> (f, (translate map (m, si, j, s) e)))
            f_e_list
        in Estruct (type_name, f_e_list)
    | Minils.Eapp ({ Minils.a_op = Minils.Efield;
                    Minils.a_params = [{ se_desc = Sconstructor f }] },
                   [e], _) ->
        let e = translate map (m, si, j, s) e in
          Elhs (mk_lhs (Lfield (lhs_of_exp e, f)))
     (*Array operators*)
    | Minils.Eapp ({ Minils.a_op = Minils.Earray }, e_list, _) ->
        Earray (List.map (translate map (m, si, j, s)) e_list)
    | Minils.Eapp ({ Minils.a_op = Minils.Eselect;
                     Minils.a_params = idx }, [e], _) ->
        let e = translate map (m, si, j, s) e in
        let idx_list = List.map (fun idx -> mk_exp (Econst idx)) idx in
          Elhs (lhs_of_idx_list (lhs_of_exp e) idx_list)
    | _ -> (*Minils_printer.print_exp stdout e; flush stdout;*) assert false
  in
    mk_exp ~ty:e.Minils.e_ty desc

(* [translate pat act = si, j, d, s] *)
and translate_act map ((m, _, _, _) as context) pat
    ({ Minils.e_desc = desc } as act) =
  match pat, desc with
    | Minils.Etuplepat p_list,
      Minils.Eapp ({ Minils.a_op = Minils.Etuple }, act_list, _) ->
        List.flatten (List.map2 (translate_act map context) p_list act_list)
    | Minils.Etuplepat p_list,
        Minils.Econst { se_desc = Stuple se_list } ->
        let const_list = List.map
          (fun se -> Minils.mk_exp (Minils.Econst se)) se_list in
          List.flatten (List.map2 (translate_act map context) p_list const_list)
    | pat, Minils.Ewhen (e, _, _) ->
        translate_act map context pat e
    | pat, Minils.Emerge (x, c_act_list) ->
        let lhs = var_from_name map x in
        [Acase (mk_exp (Elhs lhs),
               translate_c_act_list map context pat c_act_list)]
    | Minils.Evarpat n, _ ->
        [Aassgn (var_from_name map n, translate map context act)]
    | _ -> (*Minils_printer.print_exp stdout act;*) assert false

and translate_c_act_list map context pat c_act_list =
  List.map
    (fun (c, act) -> (c, (translate_act map context pat act)))
    c_act_list

let rec translate_eq map { Minils.eq_lhs = pat; Minils.eq_rhs = e }
    (m, si, j, s) =
  let { Minils.e_desc = desc; Minils.e_ty = ty;
        Minils.e_ck = ck; Minils.e_loc = loc } = e in
  match (pat, desc) with
    | Minils.Evarpat n, Minils.Efby (opt_c, e) ->
        let x = var_from_name map n in
        let si = (match opt_c with
                    | None -> si
                    | Some c ->
                        (Aassgn (x,
                                mk_exp (Econst c))) :: si) in
        let m = (n, ty) :: m in
        let action = Aassgn (var_from_name map n,
                            translate map (m, si, j, s) e)
        in
        m, si, j, (control map ck action) :: s

    | pat, Minils.Eapp ({ Minils.a_op = Minils.Efun n | Minils.Enode n;
                          Minils.a_params = params } as app,
                         e_list, r) ->
        let name_list = translate_pat map pat in
        let c_list = List.map (translate map (m, si, j, s)) e_list in
        let o = Oobj (gen_obj_name n) in
        let si =
          (match app.Minils.a_op with
             | Minils.Enode _ -> (reinit o) :: si
             | Minils.Efun _ -> si) in
        let j = (o, n, None, loc) :: j in
        let action = Acall (name_list, o, Mstep, c_list) in
        let s = (match r, app.Minils.a_op with
                   | Some r, Minils.Enode _ ->
                       let ra =
                         control map (Minils.Con (ck, Name "true", r))
                           (reinit o) in
                       ra :: (control map ck action) :: s
                   | _, _ -> (control map ck action) :: s) in
        m, si, j, s

    | Minils.Etuplepat p_list,
        Minils.Eapp({ Minils.a_op = Minils.Etuple }, act_list, _) ->
        List.fold_right2
          (fun pat e ->
             translate_eq map
               (Minils.mk_equation pat e))
          p_list act_list (m, si, j, s)

    | pat, Minils.Eapp({ Minils.a_op = Minils.Eifthenelse }, [e1;e2;e3], _) ->
        let cond = translate map (m, si, j, s) e1 in
        let m, si, j, true_act = translate_eq map
          (Minils.mk_equation pat e2) (m, si, j, s) in
        let m, si, j, false_act = translate_eq map
          (Minils.mk_equation pat e3) (m, si, j, s) in
        let action = Acase (cond, [Name "true", true_act;
                                   Name "false", false_act]) in
          m, si, j, (control map ck action) :: s

    | Minils.Evarpat x,
          Minils.Eapp ({ Minils.a_op = Minils.Efield_update;
                   Minils.a_params = [{ se_desc = Sconstructor f }] },
                  [e1; e2], _) ->
        let x = var_from_name map x in
        let copy = Aassgn (x, translate map (m, si, j, s) e1) in
        let action =
          Aassgn (mk_lhs (Lfield (x, f)), translate map (m, si, j, s) e2)
        in
        m, si, j, (control map ck copy) :: (control map ck action) :: s

    | Minils.Evarpat x,
        Minils.Eapp ({ Minils.a_op = Minils.Eselect_slice;
                       Minils.a_params = [idx1; idx2] }, [e], _) ->
        let cpt = Ident.fresh "i" in
        let e = translate map (m, si, j, s) e in
        let idx = mk_exp (Eop (op_from_string "+",
                               [mk_evar cpt;
                                mk_exp (Econst idx1) ])) in
        (* bound = (idx2 - idx1) + 1*)
        let bound =
          mk_static_exp (Sop(op_from_string "+",
                         [ mk_static_exp (Sint 1);
                           mk_static_exp (Sop (op_from_string "-",
                                                [idx2;idx1])) ])) in
        let action =
          Afor (cpt, mk_static_exp (Sint 0), bound,
               [Aassgn (mk_lhs (Larray (var_from_name map x, mk_evar cpt)),
                      mk_lhs_exp (Larray (lhs_of_exp e, idx)))] )
        in
        m, si, j, (control map ck action) :: s

    | Minils.Evarpat x,
          Minils.Eapp ({ Minils.a_op = Minils.Eselect_dyn }, e1::e2::idx, _) ->
        let x = var_from_name map x in
        let bounds = Mls_utils.bounds_list e1.Minils.e_ty in
        let e1 = translate map (m, si, j, s) e1 in
        let idx = List.map (translate map (m, si, j, s)) idx in
        let true_act =
          Aassgn (x, mk_exp (Elhs (lhs_of_idx_list (lhs_of_exp e1) idx))) in
        let false_act = Aassgn (x, translate map (m, si, j, s) e2) in
        let cond = bound_check_expr idx bounds in
        let action = Acase (cond, [ Name "true", [true_act];
                                    Name "false", [false_act] ]) in
          m, si, j, (control map ck action) :: s

    | Minils.Evarpat x,
            Minils.Eapp ({ Minils.a_op = Minils.Eupdate;
                           Minils.a_params = idx }, [e1; e2], _) ->
        let x = var_from_name map x in
        let copy = Aassgn (x, translate map (m, si, j, s) e1) in
        let idx = List.map (fun idx -> mk_exp (Econst idx)) idx in
        let action = Aassgn (lhs_of_idx_list x idx,
                            translate map (m, si, j, s) e2)
        in
        m, si, j, (control map ck copy) :: (control map ck action) :: s

    | Minils.Evarpat x,
              Minils.Eapp ({ Minils.a_op = Minils.Earray_fill;
                             Minils.a_params = [n] }, [e], _) ->
        let cpt = Ident.fresh "i" in
        let action =
          Afor (cpt, mk_static_exp (Sint 0), n,
                [Aassgn (mk_lhs (Larray (var_from_name map x,
                                 mk_evar cpt)),
                      translate map (m, si, j, s) e) ])
        in
        m, si, j, (control map ck action) :: s

    | Minils.Evarpat x,
                Minils.Eapp ({ Minils.a_op = Minils.Econcat }, [e1; e2], _) ->
        let cpt1 = Ident.fresh "i" in
        let cpt2 = Ident.fresh "i" in
        let x = var_from_name map x in
        (match e1.Minils.e_ty, e2.Minils.e_ty with
           | Tarray (_, n1), Tarray (_, n2) ->
               let e1 = translate map (m, si, j, s) e1 in
               let e2 = translate map (m, si, j, s) e2 in
               let a1 =
                 Afor (cpt1, mk_static_exp (Sint 0), n1,
                      [Aassgn (mk_lhs (Larray (x, mk_evar cpt1)),
                               mk_lhs_exp (Larray (lhs_of_exp e1,
                                                    mk_evar cpt1)))] ) in
               let idx = mk_exp (Eop (op_from_string "+",
                                      [ mk_exp (Econst n1); mk_evar cpt2])) in
               let a2 =
                 Afor (cpt2, static_exp_of_int 0, n2,
                      [Aassgn (mk_lhs (Larray (x, idx)),
                              mk_lhs_exp (Larray (lhs_of_exp e2,
                                                   mk_evar cpt2)))] )
               in
               m, si, j, (control map ck a1) :: (control map ck a2) :: s
           | _ -> assert false )

    | pat, Minils.Eiterator (it,
                             ({ Minils.a_op = Minils.Efun f | Minils.Enode f;
                               Minils.a_params = params } as app),
                          n, e_list, reset) ->
        let name_list = translate_pat map pat in
        let c_list =
          List.map (translate map (m, si, j, s)) e_list in
        let x = Ident.fresh "i" in
        let o = Oarray (gen_obj_name f, mk_lhs (Lvar x)) in
        let si =
          (match app.Minils.a_op with
             | Minils.Efun _ -> si
             | Minils.Enode _ -> (reinit o) :: si) in
        let j = (o, f, Some n, loc) :: j in
        let action = translate_iterator map it x name_list o n c_list in
        let action = List.map (control map ck) action in
        let s =
          (match reset, app.Minils.a_op with
             | Some r, Minils.Enode _ ->
                 (control map (Minils.Con (ck, Name "true", r)) (reinit o)) ::
                  action @ s
             | _, _ -> action @ s)
        in (m, si, j, s)

    | (pat, _) ->
        let action = translate_act map (m, si, j, s) pat e in
        let action = List.map (control map ck) action in
          m, si, j, action @ s

and translate_iterator map it x name_list objn n c_list =
  let array_of_output name_list =
    List.map (fun l -> mk_lhs (Larray (l, mk_evar x))) name_list in
  let array_of_input c_list =
    List.map (array_elt_of_exp (mk_lhs (Lvar x))) c_list in

  match it with
    | Minils.Imap ->
        let c_list = array_of_input c_list in
        let name_list = array_of_output name_list in
          [ Afor (x, static_exp_of_int 0, n,
               [Acall (name_list, objn, Mstep, c_list)]) ]

    | Minils.Imapfold ->
        let (c_list, acc_in) = split_last c_list in
        let c_list = array_of_input c_list in
        let (name_list, acc_out) = split_last name_list in
        let name_list = array_of_output name_list in
          [Aassgn (acc_out, acc_in);
           Afor (x, static_exp_of_int 0, n,
                 [Acall (name_list @ [ acc_out ], objn, Mstep,
                            c_list @ [ mk_exp (Elhs acc_out) ])] )]

    | Minils.Ifold ->
        let (c_list, acc_in) = split_last c_list in
        let c_list = array_of_input c_list in
        let acc_out = last_element name_list in
          [ Aassgn (acc_out, acc_in);
            Afor (x, static_exp_of_int 0, n,
                  [Acall (name_list, objn, Mstep,
                          c_list @ [ mk_exp (Elhs acc_out) ])]) ]

let translate_eq_list map act_list =
  List.fold_right (translate_eq map) act_list ([], [], [], [])

let remove m d_list =
  List.filter (fun { Minils.v_ident = n } -> not (List.mem_assoc n m)) d_list

let var_decl l =
  List.map (fun (x, t) -> mk_var_dec x t) l

let obj_decl l =
  List.map (fun (x, t, i, loc) ->
              { o_name = obj_call_name x; o_class = t;
                o_size = i; o_loc = loc }) l

let translate_var_dec map l =
  let one_var { Minils.v_ident = x; Minils.v_type = t; v_loc = loc } =
    mk_var_dec ~loc:loc x t
  in
  List.map one_var l

let translate_contract map =
  function
    | None -> ([], [], [], [], [])
    | Some
        {
          Minils.c_eq = eq_list;
          Minils.c_local = d_list;
          Minils.c_assume = e_a;
          Minils.c_enforce = e_c
        } ->
        let (m, si, j, s_list) = translate_eq_list map eq_list in
        let d_list = remove m d_list in
        let d_list = translate_var_dec map d_list in
         (m, si, j, s_list, d_list)

(** Returns a map, mapping variables names to the variables
    where they will be stored. *)
let subst_map inputs outputs locals mems =
  (* Create a map that simply maps each var to itself *)
  let m =
    List.fold_left
      (fun m { Minils.v_ident = x } -> Env.add x (mk_lhs (Lvar x)) m)
      Env.empty (inputs @ outputs @ locals)
  in
  List.fold_left (fun m x -> Env.add x (mk_lhs (Lmem x)) m) m mems

let translate_node
    {
      Minils.n_name = f;
      Minils.n_input = i_list;
      Minils.n_output = o_list;
      Minils.n_local = d_list;
      Minils.n_equs = eq_list;
      Minils.n_contract = contract;
      Minils.n_params = params;
      Minils.n_loc = loc;
    } =
  let mem_vars = List.flatten (List.map Mls_utils.Vars.memory_vars eq_list) in
  let subst_map = subst_map i_list o_list d_list mem_vars in
  let (m, si, j, s_list) = translate_eq_list subst_map eq_list in
  let (m', si', j', s_list', d_list') =
    translate_contract subst_map contract in
  let d_list = remove m d_list in
  let i_list = translate_var_dec subst_map i_list in
  let o_list = translate_var_dec subst_map o_list in
  let d_list = translate_var_dec subst_map d_list in
  let s = joinlist (s_list @ s_list') in
  let m = var_decl (m @ m') in
  let j = obj_decl (j @ j') in
  let si = joinlist (si @ si') in
  let stepm = {
    m_name = Mstep; m_inputs = i_list; m_outputs = o_list;
    m_locals = d_list @ d_list'; m_body = s } in
  let resetm = {
    m_name = Mreset; m_inputs = []; m_outputs = [];
    m_locals = []; m_body = si } in
    { cd_name = f; cd_mems = m; cd_params = params;
      cd_objs = j; cd_methods = [stepm; resetm];
      cd_loc = loc }

let translate_ty_def { Minils.t_name = name; Minils.t_desc = tdesc;
                       Minils.t_loc = loc } =
  let tdesc =
    match tdesc with
      | Minils.Type_abs -> Type_abs
      | Minils.Type_enum tag_name_list -> Type_enum tag_name_list
      | Minils.Type_struct field_ty_list ->
          Type_struct field_ty_list
  in { t_name = name; t_desc = tdesc; t_loc = loc }

let translate_const_def { Minils.c_name = name; Minils.c_value = se;
                          Minils.c_type = ty; Minils.c_loc = loc } =
  { c_name = name;
    c_value = se;
    c_type = ty;
    c_loc = loc }

let program {
  Minils.p_modname = p_modname;
  Minils.p_opened = p_module_list;
  Minils.p_types = p_type_list;
  Minils.p_nodes = p_node_list;
  Minils.p_consts = p_const_list
} =
    {
      p_modname = p_modname;
      p_opened = p_module_list;
      p_types = List.map translate_ty_def p_type_list;
      p_consts = List.map translate_const_def p_const_list;
      p_defs = List.map translate_node p_node_list;
    }


