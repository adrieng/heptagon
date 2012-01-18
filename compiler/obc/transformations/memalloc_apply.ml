open Signature
open Idents
open Signature
open Linearity
open Obc
open Obc_utils
open Obc_mapfold
open Interference_graph

module LinListEnv =
    Containers.ListMap(struct
      type t = linearity_var
      let compare = compare
    end)

let rec ivar_of_pat l = match l.pat_desc with
  | Lvar x -> Ivar x
  | Lfield(l, f) -> Ifield (ivar_of_pat l, f)
  | _ -> assert false

let rec ivar_of_ext_value w = match w.w_desc with
  | Wvar x -> Ivar x
  | Wfield(w, f) -> Ifield (ivar_of_ext_value w, f)
  | _ -> assert false

let rec repr_from_ivar env iv =
  match iv with
    | Ivar x ->
      (try
         let lhs = Env.find x env in lhs.pat_desc
       with
           Not_found -> Lvar x)
    | Ifield(iv, f) ->
      let ty = Tid (Modules.find_field f) in
      let lhs = mk_pattern ty (repr_from_ivar env iv) in
      Lfield(lhs, f)

let rec choose_record_field env l = match l with
  | [iv] -> repr_from_ivar env iv
  | (Ivar _)::l -> choose_record_field env l
  | (Ifield(iv,f))::_ -> repr_from_ivar env (Ifield(iv,f))
  | [] -> assert false

(** Chooses from a list of vars (with the same color in the interference graph)
    the one that will be used to store every other. It can be either an input,
    an output or any var if there is no input or output in the list. *)
let choose_representative m inputs outputs mems ty vars =
  let filter_ivs vars l = List.filter (fun iv -> List.mem iv l) vars in
  let inputs = filter_ivs vars inputs in
  let outputs = filter_ivs vars outputs in
  let mems = filter_ivs vars mems in
  let desc = match inputs, outputs, mems with
      | [], [], [] -> choose_record_field m vars
      | [], [], (Ivar m)::_ -> Lmem m
      | [Ivar vin], [], [] -> Lvar vin
      | [], [Ivar vout], [] -> Lvar vout
      | [Ivar vin], [Ivar _], [] -> Lvar vin
      | _, _, _ ->
        Interference.print_debug0 "@.Something is wrong with the coloring : ";
        Interference.print_debug1 "%s@." (String.concat " " (List.map ivar_to_string vars));
        Interference.print_debug0 "\tInputs : ";
        Interference.print_debug1 "%s@." (String.concat " " (List.map ivar_to_string inputs));
        Interference.print_debug0 "\tOutputs : ";
        Interference.print_debug1 "%s@." (String.concat " " (List.map ivar_to_string outputs));
        Interference.print_debug0 "\tMem : ";
        Interference.print_debug1 "%s@." (String.concat " " (List.map ivar_to_string mems));
        assert false (*something went wrong in the coloring*)
  in
    mk_pattern ty desc

let memalloc_subst_map inputs outputs mems subst_lists =
  let add_to_map (env, mutables) (ty, l) =
    let repr = choose_representative env inputs outputs mems ty l in
    let add repr env iv = match iv with
      | Ivar x -> Env.add x repr env
      | _ -> env
    in
    let env = List.fold_left (add repr) env l in
    let mutables =
      if (List.length l > 1) || (List.mem (Ivar (var_name repr)) mems) then
        IdentSet.add (var_name repr) mutables
      else
        mutables
    in
    env, mutables
  in
  List.fold_left add_to_map (Env.empty, IdentSet.empty) subst_lists

let rec lhs funs (env, mut, j) l = match l.pat_desc with
  | Lmem _ -> l, (env, mut, j)
  | Larray _ | Lfield _ -> Obc_mapfold.lhs funs (env, mut, j) l
  | Lvar _ ->
    (* replace with representative *)
    let iv = ivar_of_pat l in
    let lhs_desc = repr_from_ivar env iv in
    (* if a field is returned, recursively transform it to get a correct result *)
    let lhs_desc =
      match lhs_desc with
        | Lfield _ ->
          let newl = mk_pattern l.pat_ty lhs_desc in
          let newl, _ = lhs funs (env, mut, j) newl in
          newl.pat_desc
        | _ -> lhs_desc
    in
    { l with pat_desc = lhs_desc }, (env, mut, j)

let extvalue funs (env, mut, j) w = match w.w_desc with
  | Wmem _ | Wconst _ -> w, (env, mut, j)
  | Warray _ | Wfield _ -> Obc_mapfold.extvalue funs (env, mut, j) w
  | Wvar x ->
    (* replace with representative *)
    let lhs, _ = lhs funs (env, mut, j) (mk_pattern Signature.invalid_type (Lvar x)) in
    let neww = ext_value_of_pattern lhs in
    { w with w_desc = neww.w_desc }, (env, mut, j)

let act funs (env,mut,j) a = match a with
  | Acall_fun(pat, f, e_list) ->
      let desc = Modules.find_value f in
      let e_list = List.map (fun e -> fst (Obc_mapfold.exp_it funs (env,mut,j) e)) e_list in
      let fix_pat p a l = if Linearity.is_linear a.a_linearity then l else p::l in
      let pat = List.fold_right2 fix_pat pat desc.node_outputs [] in
      let pat = List.map (fun l -> fst (Obc_mapfold.lhs_it funs (env,mut,j) l)) pat in
      Acall_fun(pat, f, e_list), (env,mut,j)
  | Acall(pat, o, Mstep, e_list) ->
      let desc = Obc_utils.find_obj (obj_ref_name o) j in
      let e_list = List.map (fun e -> fst (Obc_mapfold.exp_it funs (env,mut,j) e)) e_list in
      let fix_pat p a l = if Linearity.is_linear a.a_linearity then l else p::l in
      let pat = List.fold_right2 fix_pat pat desc.node_outputs [] in
      let pat = List.map (fun l -> fst (Obc_mapfold.lhs_it funs (env,mut,j) l)) pat in
      Acall(pat, o, Mstep, e_list), (env,mut,j)
  | _ -> raise Errors.Fallback

let var_decs _ (env, mutables,j) vds =
  let var_dec vd acc =
    try
      if (var_name (Env.find vd.v_ident env)) <> vd.v_ident then
        (* remove unnecessary outputs *)
        acc
      else (
        let vd =
          if IdentSet.mem vd.v_ident mutables then (
            { vd with v_mutable = true }
          ) else
            vd
        in
          vd::acc
      )
    with
      | Not_found -> vd::acc
  in
    List.fold_right var_dec vds [], (env, mutables,j)


let add_other_vars md cd =
  let add_one (env, ty_env) vd =
    let should_add_var =
      is_linear vd.v_linearity &&
        (not !Compiler_options.do_mem_alloc
         || not (Interference.World.is_optimized_ty vd.v_type))
    in
    if should_add_var then
      let r = location_name vd.v_linearity in
      let env = LinListEnv.add_element r (Ivar vd.v_ident) env in
      let ty_env = LocationEnv.add r vd.v_type ty_env in
        env, ty_env
    else
      env, ty_env
  in
  let envs = List.fold_left add_one (LinListEnv.empty, LocationEnv.empty) md.m_inputs in
  let envs = List.fold_left add_one envs md.m_outputs in
  let envs = List.fold_left add_one envs md.m_body.b_locals in
  let env, ty_env = List.fold_left add_one envs cd.cd_mems in
    LinListEnv.fold (fun r x acc -> (LocationEnv.find r ty_env, x)::acc) env []

let class_def funs acc cd =
  (* find the substitution and apply it to the body of the class *)
  let ivars_of_vds vds = List.map (fun vd -> Ivar vd.v_ident) vds in
  let md = find_step_method cd in
  let inputs = ivars_of_vds md.m_inputs in
  let outputs = ivars_of_vds md.m_outputs in
  let mems = ivars_of_vds cd.cd_mems in
  (*add linear variables not taken into account by memory allocation*)
  let mem_alloc =
    if !Compiler_options.do_linear_typing then
      add_other_vars md cd
    else
      []
  in
  let mem_alloc = mem_alloc @ cd.cd_mem_alloc in
  let env, mutables = memalloc_subst_map inputs outputs mems mem_alloc in
  let cd, _ = Obc_mapfold.class_def funs (env, mutables, cd.cd_objs) cd in
  (* remove unnecessary outputs*)
  let m_outputs = List.filter (fun vd -> is_not_linear vd.v_linearity) md.m_outputs in
  let md = find_step_method cd in
  let md = { md with m_outputs = m_outputs } in
  let cd = replace_step_method md cd in
    cd, acc

let program p =
  let funs = { Obc_mapfold.defaults with class_def = class_def; var_decs = var_decs;
    act = act; lhs = lhs; extvalue = extvalue } in
  let p, _ = Obc_mapfold.program_it funs (Env.empty, IdentSet.empty, []) p in
    p
