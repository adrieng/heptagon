(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* translation from the source language to the target *)

(* $Id$ *)

open Misc
open Names 
open Ident
open Global
open Obc
open Control
open Normalize
open Memalloc
open Interference
open Static

(* merge x (C1 -> (merge y (C2 -> e2)) when C1(x)) *)

(** Targeted inputs should be marked as passed by reference. *)
let update_targeted_inputs targeting inv =
  let rec aux i = function
    | [] -> []
    | vd::l -> 
	let vd =  
	  if List.mem_assoc i targeting then (*input is targeted*)
	    { vd with v_pass_by_ref = true; }
	  else (*not targeted, leave it*)
	    vd
	in
	  vd::(aux (i+1) l) 
  in 
    aux 0 inv

let rec encode_name_params n = function
  | [] -> n
  | p::params -> encode_name_params (n^"__"^(string_of_int p)) params

let encode_longname_params n params = 
  match n with
    | Name n -> Name (encode_name_params n params)
    | Modname { qual = qual; id = id } ->
	Modname { qual = qual; id = encode_name_params id params }
	
let is_op = function
  | Modname { qual = "Pervasives"; id = _ } -> true
  | _ -> false

let op_from_string op =
  Modname { qual = "Pervasives"; id = op }

let rec lhs_of_idx_list e = function
  | [] -> e
  | idx::l -> Array(lhs_of_idx_list e l, idx)

(** Creates the expression that checks that the indices
    in idx_list are in the bounds. If idx_list=[e1;..;ep]
    and bounds = [n1;..;np], it returns
    e1 <= n1 && .. && ep <= np *)
let rec bound_check_expr idx_list bounds =
  match idx_list, bounds with
    | [idx], [n] ->
        Op (op_from_string "<", [idx; Const (Cint n)])
    | idx::idx_list, n::bounds ->
        Op (op_from_string "&", [Op (op_from_string "<", [idx; Const (Cint n)]);
		       bound_check_expr idx_list bounds])
    | _, _ -> assert false

let rec translate_type const_env = function
  | Minils.Tbase(btyp) -> translate_base_type const_env btyp
  | Minils.Tprod _     -> assert false

and translate_base_type const_env = function
  | Minils.Tint -> Tint
  | Minils.Tfloat  -> Tfloat
  | Minils.Tid(id) -> Tid(id)
  | Minils.Tarray(ty, n) -> Tarray (translate_base_type const_env ty,
				    int_of_size_exp const_env n)

let rec translate_const const_env = function
  | Minils.Cint(v) -> Cint(v)
  | Minils.Cfloat(v) -> Cfloat(v)
  | Minils.Cconstr(c) -> Cconstr(c)
  | Minils.Cconst_array(n,c) -> 
      Cconst_array(int_of_size_exp const_env n, translate_const const_env c)

let rec translate_pat map = function
  | Minils.Evarpat(x) -> [var_from_name map x]
  | Minils.Etuplepat(pat_list) ->
      List.fold_right (fun pat acc -> (translate_pat map pat) @ acc) pat_list []

(* [translate e = c] *)
let rec translate const_env map (m, si, j, s) ({ Minils.e_desc = desc } as e) =
  match desc with
    | Minils.Econst(v) -> Const(translate_const const_env v)
    | Minils.Evar(n) -> Lhs (var_from_name map n)
    | Minils.Econstvar(n) -> 
	Const (Cint(int_of_size_exp const_env (SVar n)))
    | Minils.Eop(n, _, e_list) ->
        Op(n, List.map (translate const_env map (m, si, j, s)) e_list)
    | Minils.Ewhen(e, _, _) -> translate const_env map (m, si, j, s) (e)
    | Minils.Efield(e, field) ->
	let e = translate const_env map (m, si, j, s) e in
        Lhs (Field(lhs_of_exp e, field))
    | Minils.Estruct(f_e_list) ->
        let type_name =
          begin match e.Minils.e_ty with
              Minils.Tbase(Minils.Tid(name)) -> name
            | _ -> assert false
          end in
        let f_e_list = List.map
          (fun (f, e) -> (f,
                          translate const_env map (m, si, j, s) e)) f_e_list in
        Struct(type_name,f_e_list)
(*Array operators*)	  
    | Minils.Earray e_list -> 
	ArrayLit (List.map (translate const_env map (m, si, j, s)) e_list)
    | Minils.Eselect (idx,e) -> 
	let e = translate const_env map (m, si, j, s) e in
	  Lhs ( lhs_of_idx_list (lhs_of_exp e) 
		  (List.map (fun e -> Const (Cint (int_of_size_exp const_env e))) idx) )
    | _ -> Minils.Printer.print_exp stdout e; flush stdout; assert false

(* [translate pat act = si, j, d, s] *)
and translate_act const_env map ((m,_,_,_) as context) pat ({ Minils.e_desc = desc } as act) =
  match pat, desc with
    | Minils.Etuplepat(p_list), Minils.Etuple(act_list) ->
        comp (List.map2 (translate_act const_env map context) p_list act_list)
    | pat, Minils.Ewhen(e, _, _) ->
	translate_act const_env map context pat e
    | pat, Minils.Emerge(x, c_act_list) ->
        let lhs = var_from_name map x in
          (Case(Lhs lhs, translate_c_act_list const_env map context pat c_act_list))
    | Minils.Evarpat(n), _ -> 
	Assgn(var_from_name map n, translate const_env map context act)
    | _ ->
        Minils.Printer.print_exp stdout act;
        assert false

and translate_c_act_list const_env map context pat c_act_list =
  List.map
    (fun (c, act) -> (c, translate_act const_env map context pat act))
    c_act_list

and comp s_list =
  List.fold_right (fun s rest -> Comp(s, rest)) s_list Nothing

let rec translate_eq const_env map { Minils.p_lhs = pat; Minils.p_rhs = e } (m, si, j, s) =
  let { Minils.e_desc = desc; Minils.e_ty = ty; Minils.e_ck = ck } = e in
  match pat, desc with
    | Minils.Evarpat(n), Minils.Efby(opt_c, e) ->
	let x = var_from_name map n in
        let si =
          match opt_c with
            | None -> si
            | Some(c) ->
		  if var_name x = n then 
                    (Assgn(x, Const(translate_const const_env c))) :: si
		  else
		    si (*this mem is shared, no need to add a reset intruction*)
	in
        let ty = translate_type const_env ty in
	let m = if var_name x = n then (n, ty) :: m else m in
        m, si, j,
        (control map ck (Assgn(var_from_name map n, translate const_env map (m, si, j, s) e))) :: s
    | pat, Minils.Eapp({ Minils.a_op = n }, params, e_list) ->
	let sig_info = (Modules.find_value n).info in
        let name_list = translate_pat map pat in
	let name_list = remove_targeted_outputs sig_info.targeting name_list in
        let c_list = List.map (translate const_env map (m, si, j, s)) e_list in
        let o = gen_symbol () in
        let si = (Reinit(o)) :: si in
	let params = List.map (int_of_size_exp const_env) params in
        let j = (o, encode_longname_params n params, 1) :: j in
        let s =
          (control map ck (Step_ap(name_list, Context o, c_list))) :: s in
        (m, si, j, s)
    | pat, Minils.Eevery({ Minils.a_op = n }, params, e_list, r ) ->
	let sig_info = (Modules.find_value n).info in
        let name_list = translate_pat map pat in
	let name_list = remove_targeted_outputs sig_info.targeting name_list in
        let c_list = List.map (translate const_env map (m, si, j, s)) e_list in
        let o = gen_symbol () in
        let si = (Reinit(o)) :: si in
	let params = List.map (int_of_size_exp const_env) params in
        let j = (o, encode_longname_params n params, 1) :: j in
        let s =
          (control map (Minils.Con(ck, Name("true"), r)) (Reinit(o))) ::
            (control map ck (Step_ap(name_list, Context o, c_list))) :: s in
        (m, si, j, s)
    | Minils.Etuplepat(p_list), Minils.Etuple(act_list) ->
        List.fold_right2
          (fun pat e -> translate_eq const_env map { Minils.p_lhs = pat; Minils.p_rhs = e } )
          p_list act_list (m, si, j, s)
    | Minils.Evarpat(x), Minils.Eselect_slice(idx1, idx2, e) ->
	let idx1 = int_of_size_exp const_env idx1 in
	let idx2 = int_of_size_exp const_env idx2 in
	let cpt = Ident.fresh "i" in
	let e = translate const_env map (m, si, j, s) e in
	let idx = Op(op_from_string "+", [Lhs (Var cpt); Const (Cint idx1)]) in
	let action = For(cpt, 0, idx2 - idx1 + 1,
			 Assgn (Array (var_from_name map x, Lhs (Var cpt)), 
			       Lhs (Array (lhs_of_exp e, idx))) ) in
	  m, si, j, ((control map ck action)::s)
    | Minils.Evarpat(x), Minils.Eselect_dyn (idx, bounds, e1, e2) ->
	let x = var_from_name map x in
	let e1 = translate const_env map (m, si, j, s) e1 in
	let bounds = List.map (int_of_size_exp const_env) bounds in
	let idx = List.map (translate const_env map (m, si, j, s)) idx in
	let true_act = Assgn(x, Lhs (lhs_of_idx_list (lhs_of_exp e1) idx)) in
	let false_act = Assgn(x, translate const_env map (m, si, j, s) e2) in
	let cond = bound_check_expr idx bounds in
	let action = Case(cond, [Name "true", true_act; Name "false", false_act]) in
	   m, si, j, ((control map ck action)::s)
    | Minils.Evarpat(x), Minils.Eupdate (idx, e1, e2) ->
	let x = var_from_name map x in
	let copy = Assgn (x, translate const_env map (m, si, j, s) e1) in
	let idx = List.map (fun se -> Const (Cint (int_of_size_exp const_env se))) idx in
	let action = Assgn (lhs_of_idx_list x idx,
			    translate const_env map (m, si, j, s) e2) in
	  m, si, j, ((control map ck copy)::(control map ck action)::s)
    | Minils.Evarpat(x), Minils.Erepeat (n, e) ->
	let cpt = Ident.fresh "i" in
	let action = For (cpt, 0, int_of_size_exp const_env n,
			  Assgn(Array (var_from_name map x, Lhs (Var cpt)),
			       translate const_env map (m, si, j, s) e) ) in
	  m, si, j, ((control map ck action)::s)
    | Minils.Evarpat(x), Minils.Econcat(e1, e2) ->
	let cpt1 = Ident.fresh "i" in
	let cpt2 = Ident.fresh "i" in
	let x = var_from_name map x in
	  (match e1.Minils.e_ty, e2.Minils.e_ty with
	     | Minils.Tbase(Minils.Tarray(_, n1)), Minils.Tbase(Minils.Tarray(_, n2)) ->
		 let e1 = translate const_env map (m, si, j, s) e1 in 
		 let e2 = translate const_env map (m, si, j, s) e2 in 
		 let n1 = int_of_size_exp const_env n1 in
		 let n2 = int_of_size_exp const_env n2 in
		 let a1 = For(cpt1, 0, n1, 
			     Assgn ( Array(x, Lhs(Var cpt1)), 
				   Lhs (Array(lhs_of_exp e1, Lhs(Var cpt1))) ) ) in
		 let idx = Op (op_from_string "+", [Const (Cint n1); Lhs (Var cpt2)]) in
		 let a2 = For(cpt2, 0, n2, 
			     Assgn ( Array(x, idx), 
				   Lhs (Array(lhs_of_exp e2, Lhs(Var cpt2))) ) ) in
		   m, si, j, (control map ck a1)::(control map ck a2)::s
	     | _ -> assert false
	  )
    | pat, Minils.Eiterator(it, f, params, n, e_list, reset) ->
	let sig_info = (Modules.find_value f).info in
        let name_list = translate_pat map pat in
	let name_list = remove_targeted_outputs sig_info.targeting name_list in
	let c_list = List.map (translate const_env map (m, si, j, s)) e_list in
	let o = gen_symbol () in
	let n = int_of_size_exp const_env n in
	let si = if is_op f then si else (Reinit(o)) :: si in
	let params = List.map (int_of_size_exp const_env) params in
        let j = (o, encode_longname_params f params, n) :: j in
	let x = Ident.fresh "i" in
	let action = translate_iterator const_env map it x name_list o sig_info n c_list in
	let s = 
	  (match reset with
	     | None -> (control map ck action)::s
	     | Some r -> 
		 (control map (Minils.Con(ck, Name("true"), r)) (Reinit(o))) ::
		   (control map ck action)::s
	  ) in
	  m, si, j, s
    | Minils.Evarpat(x), Minils.Efield_update (f, e1, e2) ->
	let x = var_from_name map x in
	let copy = Assgn (x, translate const_env map (m, si, j, s) e1) in
	let action = Assgn (Field(x, f),
			    translate const_env map (m, si, j, s) e2) in
	  m, si, j, ((control map ck copy)::(control map ck action)::s)
    | Minils.Etuplepat [], Minils.Ereset_mem(y, v, res) ->
	let h = Initial.ptrue, Assgn(var_from_name map y, Const (translate_const const_env v)) in
	let action = Case (Lhs (var_from_name map res), [h]) in
	  (m, si, j, (control map ck action) :: s)
    | pat, _ ->
        let action = translate_act const_env map (m, si, j, s) pat e in
        (m, si, j, (control map ck action) :: s)

and translate_iterator const_env map it x name_list o sig_info n c_list =
  match it with
    | Imap -> 
	let c_list = List.map (fun e -> Lhs (Array(lhs_of_exp e, Lhs (Var x)))) c_list in
	let name_list = List.map (fun l -> Array(l, Lhs (Var x))) name_list in
	let objn = Array_context (o, Var x) in
	  For(x, 0, n, 
	      Step_ap (name_list, objn, c_list))

    | Imapfold -> 
	let c_list, acc_in = split_last c_list in
	let c_list = List.map (fun e -> Lhs (Array(lhs_of_exp e, Lhs (Var x)))) c_list in
	let objn = Array_context (o, Var x) in

	let acc_is_targeted = (is_empty name_list)
          or (last_element sig_info.inputs).a_pass_by_ref in
	  if acc_is_targeted then (
	    (* no accumulator in output; the accumulator is modified in place *)
	    let name_list = List.map (fun l -> Array(l, Lhs (Var x))) name_list in
	    For (x, 0, n, 
		  Step_ap(name_list, objn, c_list@[acc_in]))
	  ) else (
	    (* use the output acc as accumulator*)
	    let name_list, acc_out = split_last name_list in
	    let name_list = List.map (fun l -> Array(l, Lhs (Var x))) name_list in	   
	    Comp( Assgn(acc_out, acc_in),
		  For (x, 0, n, 
			Step_ap(name_list@[acc_out], objn, c_list@[Lhs acc_out])) )
	  )

    | Ifold -> 
	let c_list, acc_in = split_last c_list in
	let c_list = List.map (fun e -> Lhs (Array(lhs_of_exp e, Lhs (Var x)))) c_list in
	let objn = Array_context (o, Var x) in

	let acc_is_targeted = (is_empty name_list) in
	  if acc_is_targeted then (
	    (* no accumulator in output; the accumulator is modified in place *)
	      For (x, 0, n, 
		    Step_ap(name_list, objn, c_list@[acc_in]))	    
	  ) else (
	    (* use the output acc as accumulator*)
	    let acc_out = last_element name_list in
	    Comp( Assgn(acc_out, acc_in),
		  For (x, 0, n,
			Step_ap(name_list, objn, c_list@[Lhs acc_out])) )
	  )

let translate_eq_list const_env map act_list =
  List.fold_right (translate_eq const_env map) act_list ([], [], [], [])

let remove m d_list =
  List.filter (fun { Minils.v_name = n } -> not (List.mem_assoc n m)) d_list

let var_decl l =
  List.map (fun (x, t) -> { v_name = x; v_type = t; v_pass_by_ref = false }) l

let obj_decl l = List.map (fun (x, t, i) -> { obj = x; cls = t; n = i }) l

let translate_var_dec const_env map l =
  let one_var { Minils.v_name = x; Minils.v_type = t } =
     { v_name = x; v_type = translate_base_type const_env t; v_pass_by_ref = false }
  in
    (* remove unused vars *)
  let l = List.filter (fun { Minils.v_name = x } -> 
			 var_name (var_from_name map x) = x) l in
    List.map one_var l

let translate_contract const_env map = function
  | None ->
      [], [], [], [], [], []
  | Some({ Minils.c_eq = eq_list;
           Minils.c_local = d_list;
           Minils.c_controllables = c_list;
           Minils.c_assume = e_a;
           Minils.c_enforce = e_c }) ->
      let m, si, j, s_list = translate_eq_list const_env map eq_list in
      let d_list = remove m d_list in
      let d_list = translate_var_dec const_env map d_list in
      let c_list = translate_var_dec const_env map c_list in
      m, si, j, s_list, d_list, c_list

let rec choose_record_field m = function
  | [IVar x] -> Var x
  | [IField(x,f)] -> Field(var_from_name m x,f)
  | (IVar x)::l -> choose_record_field m l
  | (IField(x,f))::l -> 
      if var_name (var_from_name m x) <> x then
	choose_record_field m l
      else
	Field(var_from_name m x,f)

(** Chooses from a list of vars (with the same color in the interference graph)
    the one that will be used to store every other. It can be either an input,
    an output or any var if there is no input or output in the list. *)
let choose_representative m inputs outputs mems vars =
  let ivar_mem x vars =
    match x with
      | IVar x -> List.mem x vars
      | _ -> false
  in

  let inputs = List.filter (fun var -> Minils.ivar_vd_mem var inputs) vars in
  let outputs = List.filter (fun var -> Minils.ivar_vd_mem var outputs) vars in
  let mems = List.filter (fun var -> ivar_mem var mems) vars in
    match inputs, outputs, mems with 
      | [], [], [] -> choose_record_field m vars
      | [], [], (IVar m)::_ -> Mem m
      | [IVar vin], [], [] -> Var vin
      | [], [IVar vout], [] -> Var vout
      | [IVar vin], [IVar vout], [] -> Var vin
      | _, _, _ ->
	  Format.printf "Something is wrong with the coloring : ";
	  List.iter (fun vd -> Format.printf "%s," (ivar_to_string vd)) vars;
	  Format.printf "\n Inputs : ";
	  List.iter (fun vd -> Format.printf "%s," (ivar_to_string vd)) inputs;
	  Format.printf "\n Outputs : ";
	  List.iter (fun vd -> Format.printf "%s," (ivar_to_string vd)) outputs;
	  Format.printf "\n Mem : ";
	  List.iter (fun vd -> Format.printf "%s," (ivar_to_string vd)) mems;
	  Format.printf "\n";
	  assert false (*something went wrong in the coloring*)

(** Returns a map, mapping variables names to the variables
    where they will be stored, as a result of memory allocation. *)
let subst_map_from_coloring subst_lists inputs outputs locals mems =
  let rec add_to_map map value = function
    | [] -> map
    | var::l ->
	let m = add_to_map map value l in
	(match var with
	   | IVar x -> Env.add x value m
	   | _ -> m
	)
  in
  let map_from_subst_lists m l =
    List.fold_left 
      (fun m (_,l) -> add_to_map m (choose_representative m inputs outputs mems l) l) 
      m l
  in
    if !no_mem_alloc then (
      (* Create a map that simply maps each var to itself *)
      let m = List.fold_left 
	(fun m { Minils.v_name = x } -> Env.add x (Var x) m) 
	Env.empty (inputs @ outputs @ locals) in
	List.fold_left (fun m x -> Env.add x (Mem x) m) m mems
    ) else (
      let record_lists, other_lists = List.partition
	(fun (ty,_) -> Minils.is_record_type ty) subst_lists in
      let m = map_from_subst_lists Env.empty record_lists in
	map_from_subst_lists m other_lists
    )

let translate_node_aux const_env 
    { Minils.n_name = f; Minils.n_input = i_list; Minils.n_output = o_list;
      Minils.n_local = d_list; Minils.n_equs = eq_list;
      Minils.n_contract = contract ; Minils.n_targeting = targeting; 
      Minils.n_mem_alloc = mem_alloc; Minils.n_params = params } =

  let mem_vars = List.flatten (List.map InterfRead.memory_vars eq_list) in
  let subst_map = subst_map_from_coloring mem_alloc i_list o_list d_list mem_vars in
  let m, si, j, s_list = translate_eq_list const_env subst_map eq_list in
  let m', si', j', s_list', d_list', c_list = translate_contract const_env subst_map contract in
  let d_list = remove m d_list in
  let i_list = translate_var_dec const_env subst_map i_list in
  let i_list = update_targeted_inputs targeting i_list in
  let o_list = translate_var_dec const_env subst_map o_list in
  let d_list = translate_var_dec const_env subst_map d_list in
  let s = joinlist (s_list@s_list') in
  let m = var_decl (m@m') in
  let j = obj_decl (j@j') in
  let si = joinlist (si@si') in
  let step = { inp = i_list; out = o_list; 
	       local = (d_list@d_list'@c_list);
	       controllables = c_list;
	       bd = s } in
  { cl_id = f; mem = m; objs = j; reset = si; step = step }

let build_params_list env params_names params_values =
  List.fold_left2 (fun env n v -> NamesEnv.add n (SConst v) env) env params_names params_values

let translate_node const_env n =
  let translate_one p =
    let const_env = build_params_list const_env n.Minils.n_params p in
    let c = translate_node_aux const_env n in
      { c with cl_id = encode_name_params c.cl_id p; } 
  in
    match n.Minils.n_params_instances with
      | [] -> [translate_node_aux const_env n]
      | params_lists -> List.map translate_one params_lists

let translate_ty_def const_env { Minils.t_name = name; Minils.t_desc = tdesc } =
  let tdesc = match tdesc with
    | Minils.Type_abs  -> Type_abs
    | Minils.Type_enum(tag_name_list) -> Type_enum(tag_name_list)
    | Minils.Type_struct(field_ty_list) ->
        Type_struct
          (List.map (fun (f, ty) -> (f, translate_base_type const_env ty)) field_ty_list)
  in
  { t_name = name; t_desc = tdesc }

let build_const_env cd_list =
  List.fold_left (fun env cd -> NamesEnv.add cd.Minils.c_name cd.Minils.c_value env) NamesEnv.empty cd_list

let program { Minils.p_pragmas = p_pragmas_list;
	      Minils.p_opened = p_module_list;
              Minils.p_types = p_type_list;
              Minils.p_nodes = p_node_list;
	      Minils.p_consts = p_const_list; } =
  let const_env = build_const_env p_const_list in
  { o_pragmas = p_pragmas_list;
    o_opened = p_module_list;
    o_types = List.map (translate_ty_def const_env) p_type_list;
    o_defs = List.flatten (List.map (translate_node const_env) p_node_list) }
