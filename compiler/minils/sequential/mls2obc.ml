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
open Control
open Static

let gen_obj_name n =
  (shortname n) ^ "_mem" ^ (gen_symbol ())

let rec encode_name_params n = function
  | [] -> n
  | p :: params -> encode_name_params (n ^ ("__" ^ (string_of_int p))) params

let encode_longname_params n params = match n with
  | Name n -> Name (encode_name_params n params)
  | Modname { qual = qual; id = id } ->
      Modname { qual = qual; id = encode_name_params id params; }

let op_from_string op = Modname { qual = "Pervasives"; id = op; }

let rec lhs_of_idx_list e = function
  | [] -> e | idx :: l -> Array (lhs_of_idx_list e l, idx)

let array_elt_of_exp idx e =
  match e with
    | Const (Carray (_, c)) ->
        Const c
    | _ ->
        Lhs (Array(lhs_of_exp e, Lhs idx))

(** Creates the expression that checks that the indices
    in idx_list are in the bounds. If idx_list=[e1;..;ep]
    and bounds = [n1;..;np], it returns
    e1 <= n1 && .. && ep <= np *)
let rec bound_check_expr idx_list bounds =
  match (idx_list, bounds) with
    | ([ idx ], [ n ]) -> Op (op_from_string "<", [ idx; Const (Cint n) ])
    | (idx :: idx_list, n :: bounds) ->
        Op (op_from_string "&",
            [ Op (op_from_string "<", [ idx; Const (Cint n) ]);
              bound_check_expr idx_list bounds ])
    | (_, _) -> assert false

let rec translate_type const_env = function
  | Types.Tid id when id = Initial.pint -> Tint
  | Types.Tid id when id = Initial.pfloat -> Tfloat
  | Types.Tid id when id = Initial.pbool -> Tbool
  | Types.Tid id -> Tid id
  | Types.Tarray (ty, n) ->
      Tarray (translate_type const_env ty, int_of_static_exp const_env n)
  | Types.Tprod ty -> assert false

let rec translate_const const_env = function
  | Minils.Sint v -> Cint v
  | Minils.Sbool v -> Cbool v
  | Minils.Sfloat v -> Cfloat v
  | Minils.Sconstructor c -> Cconstr c
  | Minils.Sarray_power (n, c) ->
      Carray_power (int_of_static_exp const_env n, translate_const const_env c)
  | Minils.Sarray se_list ->
      Carray (List.map (translate_const const_env) se_list)
  | Minils.Stuple se_list ->
      Ctuple (List.map (translate_const const_env) se_list)
  | Minils.Svar n -> simplify const_env (SVar n)

let rec translate_pat map = function
  | Minils.Evarpat x -> [ var_from_name map x ]
  | Minils.Etuplepat pat_list ->
      List.fold_right (fun pat acc -> (translate_pat map pat) @ acc)
        pat_list []

(* [translate e = c] *)
let rec translate const_env map (m, si, j, s)
    (({ Minils.e_desc = desc } as e)) =
  match desc with
    | Minils.Econst v -> Const (translate_const const_env v)
    | Minils.Evar n -> Lhs (var_from_name map n)
    | Minils.Ecall ({ Minils.op_name = n; Minils.op_kind = Minils.Efun },
                    e_list, _) when Mls_utils.is_op n ->
        Op (n, List.map (translate const_env map (m, si, j, s)) e_list)
    | Minils.Ewhen (e, _, _) -> translate const_env map (m, si, j, s) e
    | Minils.Efield (e, field) ->
        let e = translate const_env map (m, si, j, s) e
        in Lhs (Field (lhs_of_exp e, field))
    | Minils.Estruct f_e_list ->
        let type_name =
          (match e.Minils.e_ty with
             | Types.Tid name -> name
             | _ -> assert false) in
        let f_e_list =
          List.map
            (fun (f, e) -> (f, (translate const_env map (m, si, j, s) e)))
            f_e_list
        in Struct_lit (type_name, f_e_list)
             (*Array operators*)
    | Minils.Earray e_list ->
        Array_lit (List.map (translate const_env map (m, si, j, s)) e_list)
    | Minils.Earray_op (Minils.Eselect (idx, e)) ->
        let e = translate const_env map (m, si, j, s) e in
        let idx_list =
          List.map (fun e -> Const (Cint (int_of_static_exp const_env e))) idx
        in
        Lhs (lhs_of_idx_list (lhs_of_exp e) idx_list)
    | _ -> (*Minils_printer.print_exp stdout e; flush stdout;*) assert false

(* [translate pat act = si, j, d, s] *)
and translate_act const_env map ((m, _, _, _) as context) pat
    ({ Minils.e_desc = desc } as act) =
  match pat, desc with
    | Minils.Etuplepat p_list, Minils.Etuple act_list ->
        comp (List.map2 (translate_act const_env map context) p_list act_list)
    | pat, Minils.Ewhen (e, _, _) ->
        translate_act const_env map context pat e
    | pat, Minils.Emerge (x, c_act_list) ->
        let lhs = var_from_name map x in
        Case (Lhs lhs
                , translate_c_act_list const_env map context pat c_act_list)
    | Minils.Evarpat n, _ ->
        Assgn (var_from_name map n, translate const_env map context act)
    | _ -> (*Minils_printer.print_exp stdout act;*) assert false

and translate_c_act_list const_env map context pat c_act_list =
  List.map
    (fun (c, act) -> (c, (translate_act const_env map context pat act)))
    c_act_list

and comp s_list =
  List.fold_right (fun s rest -> Comp (s, rest)) s_list Nothing

let rec translate_eq const_env map { Minils.eq_lhs = pat; Minils.eq_rhs = e }
    (m, si, j, s) =
  let { Minils.e_desc = desc; Minils.e_ty = ty; Minils.e_ck = ck } = e in
  match (pat, desc) with
    | Minils.Evarpat n, Minils.Efby (opt_c, e) ->
        let x = var_from_name map n in
        let si = (match opt_c with
                    | None -> si
                    | Some c ->
                        (Assgn (x,
                                Const (translate_const const_env c))) :: si) in
        let ty = translate_type const_env ty in
        let m = (n, ty) :: m in
        let action = Assgn (var_from_name map n,
                            translate const_env map (m, si, j, s) e)
        in
        m, si, j, (control map ck action) :: s

    | pat, Minils.Ecall ({ Minils.op_name = n; Minils.op_params = params;
                           Minils.op_kind = (Minils.Enode
                           | Minils.Efun) as op_kind },
                         e_list, r) ->
        let name_list = translate_pat map pat in
        let c_list = List.map (translate const_env map (m, si, j, s)) e_list in
        let o = gen_obj_name n in
        let si =
          (match op_kind with
             | Minils.Enode -> (Reinit o) :: si
             | Minils.Efun -> si) in
        let params = List.map (int_of_static_exp const_env) params in
        let j = (o, (encode_longname_params n params), 1) :: j in
        let action = Step_ap (name_list, Context o, c_list) in
        let s = (match r, op_kind with
                   | Some r, Minils.Enode ->
                       let ra =
                         control map (Minils.Con (ck, Name "true", r))
                           (Reinit o) in
                       ra :: (control map ck action) :: s
                   | _, _ -> (control map ck action) :: s) in
        m, si, j, s

    | Minils.Etuplepat p_list, Minils.Etuple act_list ->
        List.fold_right2
          (fun pat e ->
             translate_eq const_env map
               (Minils.mk_equation pat e))
          p_list act_list (m, si, j, s)

    | Minils.Evarpat x, Minils.Efield_update (f, e1, e2) ->
        let x = var_from_name map x in
        let copy = Assgn (x, translate const_env map (m, si, j, s) e1) in
        let action =
          Assgn (Field (x, f), translate const_env map (m, si, j, s) e2)
        in
        m, si, j, (control map ck copy) :: (control map ck action) :: s

    | Minils.Evarpat x,
        Minils.Earray_op (Minils.Eselect_slice (idx1, idx2, e)) ->
        let idx1 = int_of_static_exp const_env idx1 in
        let idx2 = int_of_static_exp const_env idx2 in
        let cpt = Ident.fresh "i" in
        let e = translate const_env map (m, si, j, s) e in
        let idx =
          Op (op_from_string "+", [ Lhs (Var cpt); Const (Cint idx1) ]) in
        let action =
          For (cpt, 0, (idx2 - idx1) + 1,
               Assgn (Array (var_from_name map x, Lhs (Var cpt)),
                      Lhs (Array (lhs_of_exp e, idx))))
        in
        m, si, j, (control map ck action) :: s

    | Minils.Evarpat x,
          Minils.Earray_op (Minils.Eselect_dyn (idx, e1, e2)) ->
        let x = var_from_name map x in
        let bounds = Mls_utils.bounds_list e1.Minils.e_ty in
        let e1 = translate const_env map (m, si, j, s) e1 in
        let bounds = List.map (int_of_static_exp const_env) bounds in
        let idx = List.map (translate const_env map (m, si, j, s)) idx in
        let true_act =
          Assgn (x, Lhs (lhs_of_idx_list (lhs_of_exp e1) idx)) in
        let false_act =
          Assgn (x, translate const_env map (m, si, j, s) e2) in
        let cond = bound_check_expr idx bounds in
        let action =
          Case (cond,
                [ ((Name "true"), true_act); ((Name "false"), false_act) ])
        in
        m, si, j, (control map ck action) :: s

    | Minils.Evarpat x,
            Minils.Earray_op (Minils.Eupdate (idx, e1, e2)) ->
        let x = var_from_name map x in
        let copy = Assgn (x, translate const_env map (m, si, j, s) e1) in
        let idx =
          List.map (fun se -> Const (Cint (int_of_static_exp const_env se)))
            idx in
        let action = Assgn (lhs_of_idx_list x idx,
                            translate const_env map (m, si, j, s) e2)
        in
        m, si, j, (control map ck copy) :: (control map ck action) :: s

    | Minils.Evarpat x,
              Minils.Earray_op (Minils.Erepeat (n, e)) ->
        let cpt = Ident.fresh "i" in
        let action =
          For (cpt, 0, int_of_static_exp const_env n,
               Assgn (Array (var_from_name map x, Lhs (Var cpt)),
                      translate const_env map (m, si, j, s) e))
        in
        m, si, j, (control map ck action) :: s

    | Minils.Evarpat x,
                Minils.Earray_op (Minils.Econcat (e1, e2)) ->
        let cpt1 = Ident.fresh "i" in
        let cpt2 = Ident.fresh "i" in
        let x = var_from_name map x in
        (match e1.Minils.e_ty, e2.Minils.e_ty with
           | Types.Tarray (_, n1), Types.Tarray (_, n2) ->
               let e1 = translate const_env map (m, si, j, s) e1 in
               let e2 = translate const_env map (m, si, j, s) e2 in
               let n1 = int_of_static_exp const_env n1 in
               let n2 = int_of_static_exp const_env n2 in
               let a1 =
                 For (cpt1, 0, n1,
                      Assgn (Array (x, Lhs (Var cpt1)),
                             Lhs (Array (lhs_of_exp e1, Lhs (Var cpt1))))) in
               let idx =
                 Op (op_from_string "+", [ Const (Cint n1); Lhs (Var cpt2) ]) in
               let a2 =
                 For (cpt2, 0, n2,
                      Assgn (Array (x, idx),
                             Lhs (Array (lhs_of_exp e2, Lhs (Var cpt2)))))
               in
               m, si, j, (control map ck a1) :: (control map ck a2) :: s
           | _ -> assert false )

    | pat, Minils.Earray_op (
        Minils.Eiterator (it,
                          { Minils.op_name = f; Minils.op_params = params;
                            Minils.op_kind = k },
                          n, e_list, reset)) ->
        let name_list = translate_pat map pat in
        let c_list =
          List.map (translate const_env map (m, si, j, s)) e_list in
        let o = gen_obj_name f in
        let n = int_of_static_exp const_env n in
        let si =
          (match k with
             | Minils.Efun -> si
             | Minils.Enode -> (Reinit o) :: si) in
        let params = List.map (int_of_static_exp const_env) params in
        let j = (o, (encode_longname_params f params), n) :: j in
        let x = Ident.fresh "i" in
        let action =
          translate_iterator const_env map it x name_list o n c_list in
        let s =
          (match reset with
             | None -> (control map ck action) :: s
             | Some r ->
                 (control map (Minils.Con (ck, Name "true", r)) (Reinit o)) ::
                   (control map ck action) :: s )
        in (m, si, j, s)

    | (pat, _) ->
        let action = translate_act const_env map (m, si, j, s) pat e
        in (m, si, j, ((control map ck action) :: s))

and translate_iterator const_env map it x name_list o n c_list =
  match it with
    | Minils.Imap ->
        let c_list =
          List.map (array_elt_of_exp (Var x)) c_list in
        let name_list = List.map (fun l -> Array (l, Lhs (Var x))) name_list in
        let objn = Array_context (o, Var x) in
        For (x, 0, n, Step_ap (name_list, objn, c_list))

    | Minils.Imapfold ->
        let (c_list, acc_in) = split_last c_list in
        let c_list = List.map (array_elt_of_exp (Var x)) c_list in
        let objn = Array_context (o, Var x) in
        let (name_list, acc_out) = split_last name_list in
        let name_list = List.map (fun l -> Array (l, Lhs (Var x))) name_list in
        Comp (Assgn (acc_out, acc_in),
              For (x, 0, n,
                   Step_ap (name_list @ [ acc_out ], objn,
                            c_list @ [ Lhs acc_out ])))

    | Minils.Ifold ->
        let (c_list, acc_in) = split_last c_list in
        let c_list = List.map (array_elt_of_exp (Var x)) c_list in
        let objn = Array_context (o, Var x) in
        let acc_out = last_element name_list in
        Comp (Assgn (acc_out, acc_in),
              For (x, 0, n,
                   Step_ap (name_list, objn, c_list @ [ Lhs acc_out ])))

let translate_eq_list const_env map act_list =
  List.fold_right (translate_eq const_env map) act_list ([], [], [], [])

let remove m d_list =
  List.filter (fun { Minils.v_ident = n } -> not (List.mem_assoc n m)) d_list

let var_decl l =
  List.map (fun (x, t) -> mk_var_dec x t) l

let obj_decl l = List.map (fun (x, t, i) -> { obj = x; cls = t; size = i; }) l

let translate_var_dec const_env map l =
  let one_var { Minils.v_ident = x; Minils.v_type = t } =
    mk_var_dec x (translate_type const_env t)
  in
  List.map one_var l

let translate_contract const_env map =
  function
    | None -> ([], [], [], [], [], [])
    | Some
        {
          Minils.c_eq = eq_list;
          Minils.c_local = d_list;
          Minils.c_controllables = c_list;
          Minils.c_assume = e_a;
          Minils.c_enforce = e_c
        } ->
        let (m, si, j, s_list) = translate_eq_list const_env map eq_list in
        let d_list = remove m d_list in
        let d_list = translate_var_dec const_env map d_list in
        let c_list = translate_var_dec const_env map c_list
        in (m, si, j, s_list, d_list, c_list)

(** Returns a map, mapping variables names to the variables
    where they will be stored. *)
let subst_map inputs outputs locals mems =
  (* Create a map that simply maps each var to itself *)
  let m =
    List.fold_left (fun m { Minils.v_ident = x } -> Env.add x (Var x) m)
      Env.empty (inputs @ outputs @ locals)
  in
  List.fold_left (fun m x -> Env.add x (Mem x) m) m mems

let translate_node_aux const_env
    {
      Minils.n_name = f;
      Minils.n_input = i_list;
      Minils.n_output = o_list;
      Minils.n_local = d_list;
      Minils.n_equs = eq_list;
      Minils.n_contract = contract;
      Minils.n_params = params
    } =
  let mem_vars = List.flatten (List.map Mls_utils.Vars.memory_vars eq_list) in
  let subst_map = subst_map i_list o_list d_list mem_vars in
  let (m, si, j, s_list) = translate_eq_list const_env subst_map eq_list in
  let (m', si', j', s_list', d_list', c_list) =
    translate_contract const_env subst_map contract in
  let d_list = remove m d_list in
  let i_list = translate_var_dec const_env subst_map i_list in
  let o_list = translate_var_dec const_env subst_map o_list in
  let d_list = translate_var_dec const_env subst_map d_list in
  let s = joinlist (s_list @ s_list') in
  let m = var_decl (m @ m') in
  let j = obj_decl (j @ j') in
  let si = joinlist (si @ si') in
  let step =
    {
      inp = i_list;
      out = o_list;
      local = d_list @ (d_list' @ c_list);
      controllables = c_list;
      bd = s;
    }
  in
  { cl_id = f; mem = m; objs = j; reset = si; step = step; }

let build_params_list env params_names params_values =
  List.fold_left2 (fun env { p_name = n }  v -> NamesEnv.add n (Sconst v) env)
    env params_names params_values

let translate_node const_env n =
  let translate_one p =
    let const_env = build_params_list const_env n.Minils.n_params p in
    let c = translate_node_aux const_env n
    in
    { c with cl_id = encode_name_params c.cl_id p; }
  in
  match n.Minils.n_params_instances with
    | [] -> [ translate_node_aux const_env n ]
    | params_lists -> List.map translate_one params_lists

let translate_ty_def const_env { Minils.t_name = name; Minils.t_desc = tdesc
                               } =
  let tdesc =
    match tdesc with
      | Minils.Type_abs -> Type_abs
      | Minils.Type_enum tag_name_list -> Type_enum tag_name_list
      | Minils.Type_struct field_ty_list ->
          Type_struct
            (List.map
               (fun { f_name = f; f_type = ty } ->
                  (f, translate_type const_env ty))
               field_ty_list)
  in { t_name = name; t_desc = tdesc; }

let build_const_env cd_list =
  List.fold_left
    (fun env cd -> NamesEnv.add cd.Minils.c_name cd.Minils.c_value env)
    NamesEnv.empty cd_list

let program {
  Minils.p_pragmas = p_pragmas_list;
  Minils.p_opened = p_module_list;
  Minils.p_types = p_type_list;
  Minils.p_nodes = p_node_list;
  Minils.p_consts = p_const_list
} =
  let const_env = build_const_env p_const_list
  in
  {
    o_pragmas = p_pragmas_list;
    o_opened = p_module_list;
    o_types = List.map (translate_ty_def const_env) p_type_list;
    o_defs = List.flatten (List.map (translate_node const_env) p_node_list);
  }


