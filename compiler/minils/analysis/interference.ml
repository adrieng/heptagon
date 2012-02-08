open Idents
open Types
open Signature
open Clocks
open Minils
open Linearity
open Interference_graph
open Containers
open Printf

let print_interference_graphs = false
let verbose_mode = false
let print_debug0 s =
  if verbose_mode then
    Format.printf s

let print_debug1 fmt x =
  if verbose_mode then
    Format.printf fmt x

let print_debug2 fmt x y =
  if verbose_mode then
    Format.printf fmt x y

let print_debug_ivar_env name env =
  if verbose_mode then (
    Format.printf "%s:  " name;
    IvarEnv.iter (fun k v -> Format.printf "%s : %d; " (ivar_to_string k) v) env;
    Format.printf "@."
  )

module TyEnv =
    ListMap(struct
      type t = ty
      let compare = Global_compare.type_compare
    end)

(** @return whether [ty] corresponds to a record type. *)
let is_record_type ty = match Modules.unalias_type ty with
  | Tid n ->
      (match Modules.find_type n with
        | Tstruct _ -> true
        | _ -> false)
  | _ -> false

let is_array_or_struct ty =
  match Modules.unalias_type ty with
    | Tarray _ -> true
    | Tid n ->
        (match Modules.find_type n with
          | Signature.Tstruct _ -> true
          | _ -> false)
    | _ -> false

let is_enum ty = match Modules.unalias_type ty with
  | Tid n ->
      (match Modules.find_type n with
        | Tenum _ -> true
        | _ -> false)
  | _ -> false

module InterfRead = struct
  exception Const_extvalue

  let rec vars_ck acc = function
    | Con(_, _, n) -> IvarSet.add (Ivar n) acc
    | Cbase | Cvar { contents = Cindex _ } -> acc
    | Cvar { contents = Clink ck } -> vars_ck acc ck

  let rec vars_ct acc ct = match ct with
    | Ck ck -> vars_ck acc ck
    | Cprod ct_list -> List.fold_left vars_ct acc ct_list

  let rec ivar_of_extvalue w = match w.w_desc with
    | Wvar x -> Ivar x
    | Wfield(w, f) -> Ifield (ivar_of_extvalue w, f)
    | Wwhen(w, _, _) -> ivar_of_extvalue w
    | Wconst _ -> raise Const_extvalue
    | Wreinit (_, w) -> ivar_of_extvalue w

  let ivar_of_pat p = match p with
    | Evarpat x -> Ivar x
    | _ -> assert false

  let ivars_of_extvalues wl =
    let tr_one acc w =
      try
        (ivar_of_extvalue w)::acc
      with
        | Const_extvalue -> acc
    in
      List.fold_left tr_one [] wl

  let read_extvalue funs acc w =
    (* recursive call *)
    let _, acc = Mls_mapfold.extvalue funs acc w in
    let acc =
      try
        IvarSet.add (ivar_of_extvalue w) acc
      with
        | Const_extvalue -> acc
    in
      w, vars_ck acc w.w_ck

  let read_exp funs acc e =
    (* recursive call *)
    let _, acc = Mls_mapfold.exp funs acc e in
    (* special cases *)
    let acc = match e.e_desc with
      | Emerge(x,_)  | Eapp(_, _, Some x)
      | Eiterator (_, _, _, _, _, Some x) -> IvarSet.add (Ivar x) acc
      | _ -> acc
    in
      e, vars_ct acc e.e_ct

  let rec vars_pat acc = function
    | Evarpat x -> IvarSet.add (Ivar x) acc
    | Etuplepat pat_list -> List.fold_left vars_pat acc pat_list

  let def eq =
    vars_pat IvarSet.empty eq.eq_lhs

  let rec nth_var_from_pat j pat =
    match j, pat with
      | 0, Evarpat x -> x
      | n, Etuplepat l -> nth_var_from_pat 0 (List.nth l n)
      | _, _ -> assert false

  let read_exp e =
    let funs = { Mls_mapfold.defaults with
      Mls_mapfold.exp = read_exp;
      Mls_mapfold.extvalue = read_extvalue } in
    let _, acc =  Mls_mapfold.exp_it funs IvarSet.empty e in
      acc

  let read eq =
    read_exp eq.eq_rhs
end


module World = struct
  let vds = ref Env.empty
  let memories = ref IvarSet.empty
  let igs = ref []

  let init f =
    (* build vds cache *)
    let build env vds =
      List.fold_left (fun env vd -> Env.add vd.v_ident vd env) env vds
    in
    let env = build Env.empty f.n_input in
    let env = build env f.n_output in
    let env = build env f.n_local in
      igs := [];
      vds := env;
    (* build the set of memories *)
      let mems = Mls_utils.node_memory_vars f in
        memories := List.fold_left (fun s (x, _) -> IvarSet.add (Ivar x) s) IvarSet.empty mems

  let vd_from_ident x =
    Env.find x !vds

  let rec ivar_type iv = match iv with
    | Ivar x ->
        let vd = vd_from_ident x in
          vd.v_type
    | Ifield(_, f) ->
        let n = Modules.find_field f in
        let fields = Modules.find_struct n in
          Signature.field_assoc f fields

  let is_optimized_ty ty =
    (!Compiler_options.interf_all (* && not (is_enum ty)) *) ) || is_array_or_struct ty

  let is_optimized iv =
    is_optimized_ty (ivar_type iv)

  let is_memory x =
    IvarSet.mem (Ivar x) !memories

  let node_for_ivar iv =
    let rec _node_for_ivar igs iv =
      match igs with
        | [] -> print_debug1 "Var not in graph: %s@." (ivar_to_string iv); raise Not_found
        | ig::igs ->
            (try
                ig, node_for_value ig iv
              with Not_found ->
                _node_for_ivar igs iv)
    in
      _node_for_ivar !igs iv

  let node_for_name x =
    node_for_ivar (Ivar x)
end

(** Helper functions to work with the multiple interference graphs *)

let by_ivar def f x y =
  if World.is_optimized x then (
    let igx, nodex = World.node_for_ivar x in
    let igy, nodey = World.node_for_ivar y in
      if igx == igy then
        f igx nodex nodey
      else
        def
  ) else
    def

let by_name def f x y =
  if World.is_optimized (Ivar x) then (
    let igx, nodex = World.node_for_name x in
    let igy, nodey = World.node_for_name y in
      if igx == igy then
        f igx nodex nodey
      else
        def
  ) else
    def

let add_interference_link_from_name = by_name () add_interference_link
let add_interference_link_from_ivar = by_ivar () add_interference_link
let add_affinity_link_from_name = by_name () add_affinity_link
let add_affinity_link_from_ivar = by_ivar () add_affinity_link
let add_same_value_link_from_name = by_name () add_affinity_link
let add_same_value_link_from_ivar = by_ivar () add_affinity_link
let coalesce_from_name = by_name () coalesce
let coalesce_from_ivar = by_ivar () coalesce
let have_same_value_from_name = by_name false have_same_value

let remove_from_ivar iv =
  try
    let ig, v = World.node_for_ivar iv in
      G.remove_vertex ig.g_graph v
  with
    | Not_found -> (* var not in graph, just ignore it *) ()


(** Adds all the fields of a variable to the set [s] (when it corresponds to a record). *)
let rec all_ivars s iv ty =
  let s = if World.is_optimized_ty ty then IvarSet.add iv s else s in
  match Modules.unalias_type ty with
    | Tid n ->
        (try
            let fields = Modules.find_struct n in
              List.fold_left (fun s { f_name = n; f_type = ty } ->
                all_ivars s (Ifield(iv, n)) ty) s fields
          with
              Not_found -> s
        )
    | _ -> s

let all_ivars_set ivs =
  IvarSet.fold (fun iv s -> all_ivars s iv (World.ivar_type iv)) ivs IvarSet.empty


(** Returns a map giving the number of uses of each ivar in the equations [eqs]. *)
let compute_uses eqs =
  let aux env eq =
    let incr_uses iv env =
      if IvarEnv.mem iv env then
        IvarEnv.add iv ((IvarEnv.find iv env) + 1) env
      else
        IvarEnv.add iv 1 env
    in
    let ivars = all_ivars_set (InterfRead.read eq) in
      IvarSet.fold incr_uses ivars env
  in
    List.fold_left aux IvarEnv.empty eqs

let number_uses iv uses =
  try
    IvarEnv.find iv uses
  with
    | Not_found ->
        (* add one use for memories without any use to make sure they interfere
           with other memories and outputs. *)
        (match iv with
          | Ivar x when World.is_memory x -> 1
          | _ -> 0)

let add_uses uses iv env =
  let ivars = all_ivars IvarSet.empty iv (World.ivar_type iv) in
    IvarSet.fold (fun iv env -> IvarEnv.add iv (number_uses iv uses) env) ivars env

let decr_uses iv env =
  try
    IvarEnv.add iv ((IvarEnv.find iv env) - 1) env
  with
    | Not_found ->
        print_debug1 "Cannot decrease; var not found : %s@." (ivar_to_string iv); assert false

(** TODO: compute correct live range for variables wit no use ?*)
let compute_live_vars eqs =
  let uses = compute_uses eqs in
  print_debug_ivar_env "Uses" uses;
  let aux (env,res) eq =
    let alive_vars = IvarEnv.fold (fun iv n acc -> if n > 0 then iv::acc else acc) env [] in
      print_debug1 "Alive vars : %s@." (String.concat " " (List.map ivar_to_string alive_vars));
      let read_ivars = all_ivars_set (InterfRead.read eq) in
      let env = IvarSet.fold decr_uses read_ivars env in
      let res = (eq, alive_vars)::res in
      let env = IvarSet.fold (add_uses uses) (InterfRead.def eq) env in
        print_debug_ivar_env "Remaining uses" env;
        env, res
  in
  let env = IvarSet.fold (add_uses uses) !World.memories IvarEnv.empty in
  let _, res = List.fold_left aux (env, []) eqs in
    res


let rec disjoint_clock is_mem ck1 ck2 =
  match Clocks.ck_repr ck1, Clocks.ck_repr ck2 with
    | Cbase, Cbase -> false
    | Con(ck1, c1, n1), Con(ck2,c2,n2) ->
        if ck1 = ck2 & n1 = n2  & c1 <> c2 & not is_mem then
          true
        else
          disjoint_clock is_mem ck1 ck2
        (*let separated_by_reset =
          (match x_is_mem, y_is_mem with
            | true, true -> are_separated_by_reset c1 c2
            | _, _ -> true) in *)
    | _ -> false

(** [should_interfere x y] returns whether variables x and y
    can interfere. *)
let should_interfere (x, y) =
  let vdx = World.vd_from_ident x in
  let vdy = World.vd_from_ident y in
  if Global_compare.type_compare vdx.v_type vdy.v_type <> 0 then
    false
  else (
    let x_is_mem = World.is_memory x in
    let y_is_mem = World.is_memory y in
    let are_copies = have_same_value_from_name x y in
    let disjoint_clocks = disjoint_clock (x_is_mem || y_is_mem) vdx.v_clock vdy.v_clock in
      not (disjoint_clocks or are_copies)
  )

let should_interfere = Misc.memoize_couple should_interfere

(** Builds the (empty) interference graphs corresponding to the
    variable declaration list vds. It just creates one graph per type
    and one node per declaration. *)
let init_interference_graph () =
  (** Adds a node for the variable and all fields of a variable. *)
  let rec add_ivar env iv ty =
    let ivars = all_ivars IvarSet.empty iv ty in
      IvarSet.fold (fun iv env -> TyEnv.add_element (World.ivar_type iv) (mk_node iv) env) ivars env
  in
  let env = Env.fold
    (fun _ vd env -> add_ivar env (Ivar vd.v_ident) vd.v_type) !World.vds TyEnv.empty in
    World.igs := TyEnv.fold (fun ty l acc -> (mk_graph l ty)::acc) env []


(** Adds interferences between all the variables in
    the list. If force is true, then interference is added
    whatever the variables are, without checking if interference
    is real. *)
let rec add_interferences_from_list force vars =
  let add_interference x y =
    match x, y with
      | Ivar x, Ivar y ->
        if force or should_interfere (x, y) then
          add_interference_link_from_ivar (Ivar x) (Ivar y)
      | _, _ -> add_interference_link_from_ivar x y
  in
    Misc.iter_couple add_interference vars

(** Adds to the interference graphs [igs] the
    interference resulting from the live vars sets
    stored in hash. *)
let add_interferences live_vars =
  List.iter (fun (_, vars) -> add_interferences_from_list false vars) live_vars

(** Spill non linear inputs. *)
let spill_inputs f =
  let spilled_inp = List.filter (fun vd -> not (is_linear vd.v_linearity)) f.n_input in
  let spilled_inp = List.fold_left
    (fun s vd -> IvarSet.add (Ivar vd.v_ident) s) IvarSet.empty spilled_inp in
  let spilled_inp = all_ivars_set spilled_inp in
    IvarSet.iter remove_from_ivar spilled_inp

(** If we optimize all types, we need to spill outputs and memories so
    that register allocation by the C compiler is not disturbed. *)
let spill_mems_outputs f =
  let add_output s vd =
    if not (is_array_or_struct vd.v_type) then IvarSet.add (Ivar vd.v_ident) s else s
  in
  let add_memory iv s =
    if not (is_array_or_struct (World.ivar_type iv)) then IvarSet.add iv s else s
  in
  let spilled_vars = List.fold_left add_output IvarSet.empty f.n_output in
  let spilled_vars = IvarSet.fold add_memory spilled_vars !World.memories in
  let spilled_vars = all_ivars_set spilled_vars in
  IvarSet.iter remove_from_ivar spilled_vars

(** [filter_vars l] returns a list of variables whose fields appear in
    a list of ivar.*)
let rec filter_fields = function
  | [] -> []
  | (Ifield (id, _))::l -> id::(filter_fields l)
  | _::l -> filter_fields l

(** Adds the interference between records variables
    caused by interferences between their fields. *)
let add_records_field_interferences () =
  let add_record_interf g n1 n2 =
    if interfere g n1 n2 then
      let v1 = filter_fields !(G.V.label n1) in
      let v2 = filter_fields !(G.V.label n2) in
        Misc.iter_couple_2 add_interference_link_from_ivar v1 v2
  in
    List.iter (iter_interf add_record_interf) !World.igs



(** Coalesce the nodes corresponding to all semilinear variables
    with the same location. *)
let coalesce_linear_vars () =
  let coalesce_one_var _ vd memlocs =
    if World.is_optimized_ty vd.v_type then
      (match vd.v_linearity with
        | Ltop -> memlocs
        | Lat r ->
            if LocationEnv.mem r memlocs then (
              coalesce_from_name vd.v_ident (LocationEnv.find r memlocs);
              memlocs
            ) else
              LocationEnv.add r vd.v_ident memlocs
        | _ -> assert false)
    else
      memlocs
  in
    ignore (Env.fold coalesce_one_var !World.vds LocationEnv.empty)

let find_targeting f =
  let find_output outputs_lins (acc,i) l =
    match l with
      | Lvar _ ->
          let idx = Misc.index (fun l1 -> l = l1) outputs_lins in
            if idx >= 0 then
              (i, idx)::acc, i+1
            else
              acc, i+1
      | _ -> acc, i+1
  in
  let desc = Modules.find_value f in
  let inputs_lins = linearities_of_arg_list desc.node_inputs in
  let outputs_lins = linearities_of_arg_list desc.node_outputs in
  let acc, _ = List.fold_left (find_output outputs_lins) ([], 0) inputs_lins in
    acc


(** [process_eq igs eq] adds to the interference graphs igs
    the links corresponding to the equation. Interferences
    corresponding to live vars sets are already added by build_interf_graph.
*)
let process_eq ({ eq_lhs = pat; eq_rhs = e } as eq) =
  (** Other cases*)
  match pat, e.e_desc with
    | _, Eiterator((Imap|Imapi), { a_op = Enode _ | Efun _ }, _, pw_list, w_list, _) ->
      let invars = InterfRead.ivars_of_extvalues w_list in
      let pinvars = InterfRead.ivars_of_extvalues pw_list in
      let outvars = IvarSet.elements (InterfRead.def eq) in
        (* because of the encoding of the fold, the outputs are written before
           the partially applied inputs are read so they must interfere *)
         List.iter (fun inv -> List.iter (add_interference_link_from_ivar inv) outvars) pinvars;
        (* affinities between inputs and outputs *)
        List.iter (fun inv -> List.iter
          (add_affinity_link_from_ivar inv) outvars) invars;
    | Evarpat x, Eiterator((Ifold|Ifoldi), { a_op = Enode _ | Efun _ }, _, pw_list, w_list, _) ->
        (* because of the encoding of the fold, the output is written before
           the inputs are read so they must interfere *)
        let w_list, _ = Misc.split_last w_list in
        let invars = InterfRead.ivars_of_extvalues w_list in
        let pinvars = InterfRead.ivars_of_extvalues pw_list in
          List.iter (add_interference_link_from_ivar (Ivar x)) invars;
          List.iter (add_interference_link_from_ivar (Ivar x)) pinvars
    | Etuplepat l, Eiterator(Imapfold, { a_op = Enode _ | Efun _ }, _, pw_list, w_list, _) ->
        let w_list, _ = Misc.split_last w_list in
        let invars = InterfRead.ivars_of_extvalues w_list in
        let pinvars = InterfRead.ivars_of_extvalues pw_list in
        let outvars, acc_out = Misc.split_last (List.map InterfRead.ivar_of_pat l) in
          (* because of the encoding of the fold, the output is written before
             the inputs are read so they must interfere *)
          List.iter (add_interference_link_from_ivar acc_out) invars;
          List.iter (add_interference_link_from_ivar acc_out) pinvars;
          (* because of the encoding of the fold, the outputs are written before
           the partially applied inputs are read so they must interfere *)
         List.iter (fun inv -> List.iter (add_interference_link_from_ivar inv) outvars) pinvars;
          (* it also interferes with outputs. We add it here because it will not hold
             if it is not used. *)
          List.iter (add_interference_link_from_ivar acc_out) outvars;
          (*affinity between inputs and outputs*)
          List.iter (fun inv -> List.iter (add_affinity_link_from_ivar inv) outvars) invars
    | Evarpat x, Efby(_, w) -> (* x  = _ fby y *)
      (try
         add_affinity_link_from_ivar (InterfRead.ivar_of_extvalue w) (Ivar x)
       with
         | InterfRead.Const_extvalue -> ())
    | Evarpat x, Eapp({ a_op = Eupdate | Efield_update }, args, _) ->
      let w,  _ = Misc.assert_1min args in
      (try
        add_same_value_link_from_ivar (InterfRead.ivar_of_extvalue w) (Ivar x)
       with
         | InterfRead.Const_extvalue -> ())
    | Evarpat x, Eextvalue w ->
      (* Add links between variables with the same value *)
      (try
        add_same_value_link_from_ivar (InterfRead.ivar_of_extvalue w) (Ivar x)
       with
         | InterfRead.Const_extvalue -> ())
    | _ -> () (* do nothing *)

(** Add the special init and return equations to the dependency graph
    (resp at the bottom and top) *)
let add_init_return_eq f =
   (** a_1,..,a_p = __init__  *)
  let eq_init = mk_equation false (Mls_utils.pat_from_dec_list f.n_input)
    (mk_extvalue_exp Cbase Initial.tint Ltop (Wconst (Initial.mk_static_int 0))) in
    (** __return__ = o_1,..,o_q *)
  let eq_return = mk_equation false (Etuplepat [])
    (mk_exp Cbase Tinvalid Ltop (Mls_utils.tuple_from_dec_list f.n_output)) in
    (eq_init::f.n_equs)@[eq_return]


let build_interf_graph f =
  World.init f;
  (** Init interference graph *)
  init_interference_graph ();

  let eqs = add_init_return_eq f in
  (** Build live vars sets for each equation *)
  let live_vars = compute_live_vars eqs in
    (* Coalesce linear variables *)
    coalesce_linear_vars ();
    (** Other cases*)
    List.iter process_eq f.n_equs;
    (* Add interferences from live vars set*)
    add_interferences live_vars;
    (* Add interferences between records implied by IField values*)
    add_records_field_interferences ();
    (* Splill inputs that are not modified *)
    spill_inputs f;
    (* Spill outputs and memories that are not arrays or struts*)
    if !Compiler_options.interf_all then
      spill_mems_outputs f;

    (* Return the graphs *)
    !World.igs



(** Color the nodes corresponding to fields using
    the color attributed to the record. This makes sure that
    if a and b are shared, then a.f and b.f are too. *)
let color_fields ig =
  let process n =
    let fields = filter_fields !(G.V.label n) in
    match fields with
      | [] -> ()
      | id::_ -> (* we only look at the first as they will all have the same color *)
        let _, top_node = World.node_for_ivar id in
          G.Mark.set n (G.Mark.get top_node)
  in
    G.iter_vertex process ig.g_graph

(** Color an interference graph.*)
let color_interf_graphs igs =
  let record_igs, igs =
    List.partition (fun ig -> is_record_type ig.g_type) igs in
    (* First color interference graphs of record types *)
    List.iter Dcoloring.color record_igs;
    (* Then update fields colors *)
    List.iter color_fields igs;
    (* and finish the coloring *)
    List.iter Dcoloring.color igs

let print_graphs f igs =
  let cpt = ref 0 in
  let print_graph ig =
    let s = (Names.shortname f.n_name)^ (string_of_int !cpt) in
      Interference2dot.print_graph (Names.fullname f.n_name) s ig;
      cpt := !cpt + 1
  in
    List.iter print_graph igs

(** Create the list of lists of variables stored together,
    from the interference graph.*)
let create_subst_lists igs =
  let create_one_ig ig =
    List.map (fun x -> ig.g_type, x) (Dcoloring.values_by_color ig)
  in
    List.flatten (List.map create_one_ig igs)

let node _ acc f =
  (** Build the interference graphs *)
  let igs = build_interf_graph f in
    (** Color the graph *)
    color_interf_graphs igs;
    if print_interference_graphs then
      print_graphs f igs;
    (** Remember the choice we made for code generation *)
      { f with n_mem_alloc = create_subst_lists igs }, acc

let program p =
  let funs = { Mls_mapfold.defaults with Mls_mapfold.node_dec = node } in
  let p, _ = Mls_mapfold.program_it funs () p in
    p
