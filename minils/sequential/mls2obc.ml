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
	Array (List.map (translate const_env map (m, si, j, s)) e_list)
    | Minils.Eselect (idx,e) -> 
	let e = translate const_env map (m, si, j, s) e in
	Lhs ( Array (lhs_of_exp e, 
		     List.map (int_of_size_exp const_env) idx) )
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
          (control map ck (Step_ap(name_list, o, c_list))) :: s in
        (m, si, j, s)
    | pat, Minils.Eevery({ Minils.a_op = n }, params, e_list, r ) ->
        let name_list = translate_pat map pat in
        let c_list = List.map (translate const_env map (m, si, j, s)) e_list in
        let o = gen_symbol () in
        let si = (Reinit(o)) :: si in
	let params = List.map (int_of_size_exp const_env) params in
        let j = (o, encode_longname_params n params, 1) :: j in
        let s =
          (control map (Minils.Con(ck, Name("true"), r)) (Reinit(o))) ::
            (control map ck (Step_ap(name_list, o, c_list))) :: s in
        (m, si, j, s)
    | Minils.Etuplepat(p_list), Minils.Etuple(act_list) ->
        List.fold_right2
          (fun pat e -> translate_eq const_env map { Minils.p_lhs = pat; Minils.p_rhs = e } )
          p_list act_list (m, si, j, s)
    | Minils.Evarpat(x), Minils.Eselect_slice(idx1, idx2, e) ->
	let idx1 = int_of_size_exp const_env idx1 in
	let idx2 = int_of_size_exp const_env idx2 in
	let idx = 
	let cpt = name (Ident.fresh "i") in
	let e = translate const_env map (m, si, j, s) e in
	let action = For( cpt, 0, idx2 - idx1 + 1,
			 Assgn (Array (var_from_name map x, Var cpt), 
			       Lhs (Array (lhs_of_exp e, idx))) )

	let action = Array_select_slice (var_from_name map x, 
					 translate const_env map (m, si, j, s) e,
					 int_of_size_exp const_env idx1,
					 int_of_size_exp const_env idx2) in
	  m, si, j, ((control map ck action)::s)
    | Minils.Evarpat(x), Minils.Eselect_dyn (idx, bounds, e1, e2) ->
	let action = Array_select_dyn (var_from_name map x, 
				       translate const_env map (m, si, j, s) e1,
				       List.map (translate const_env map (m, si, j, s)) idx,
				       List.map (int_of_size_exp const_env) bounds,
				       translate const_env map (m, si, j, s) e2 ) in
	   m, si, j, ((control map ck action)::s)
    | Minils.Evarpat(x), Minils.Eupdate (idx, e1, e2) ->
	let x = var_from_name map x in
	let copy = Assgn (x, translate const_env map (m, si, j, s) e1) in
	let action = Assgn (Array (x, List.map (int_of_size_exp const_env) idx),
			    translate const_env map (m, si, j, s) e2) in
	  m, si, j, ((control map ck copy)::(control map ck action)::s)
    | Minils.Evarpat(x), Minils.Erepeat (n, e) ->
	let cpt = name (Ident.fresh "i") in
	let action = For (cpt, 0, int_of_size_exp const_env n,
			  Assgn(Lhs (var_from_name map x, Var cpt),
			       translate const_env map (m, si, j, s) e) in
	  m, si, j, ((control map ck action)::s)
    | Minils.Evarpat(x), Minils.Econcat(e1, e2) ->
	let action = Array_concat (var_from_name map x, translate const_env map (m, si, j, s) e1,
				  translate const_env map (m, si, j, s) e2) in
	  m, si, j, ((control map ck action)::s)	
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
	let action = Array_iterate (name_list, it, o, n, c_list) in
	let s = 
	  (match reset with
	     | None -> (control map ck action)::s
	     | Some r -> 
		 (control map (Minils.Con(ck, Name("true"), r)) (Reinit(o))) ::
		   (control map ck action)::s
	  ) in
	  m, si, j, s
    | Minils.Evarpat(x), Minils.Efield_update (f, e1, e2) ->
	let action = Field_update (var_from_name map x, translate const_env map (m,si,j,s) e1,
				   f, translate const_env map (m,si,j,s) e2) in
	  m, si, j, ((control map ck action)::s)
    | Minils.Etuplepat [], Minils.Ereset_mem(y, v, res) ->
	let h = Initial.ptrue, Assgn(var_from_name map y, Const (translate_const const_env v)) in
	let action = Case (Lhs (var_from_name map res), [h]) in
	  (m, si, j, (control map ck action) :: s)
    | pat, _ ->
        let action = translate_act const_env map (m, si, j, s) pat e in
        (m, si, j, (control map ck action) :: s)

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
