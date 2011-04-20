open Idents
open Types
open Clocks
open Signature
open Minils
open Interference_graph
open Printf

let memalloc_debug = true

module TyEnv =
    ListMap(struct
      type t = ty
      let compare = Global_compare.type_compare
    end)

module InterfRead = struct
  let rec vars_ck acc = function
    | Con(_, _, n) -> IvarSet.add (Ivar n) acc
    | Cbase | Cvar { contents = Cindex _ } -> acc
    | Cvar { contents = Clink ck } -> vars_ck acc ck

  let rec ivar_of_extvalue w = match w.w_desc with
    | Wvar x -> Ivar x
    | Wfield(w, f) -> Ifield (ivar_of_extvalue w, f)
    | Wwhen(w, _, _) -> ivar_of_extvalue w
    | Wconst _ -> assert false

  let ivars_of_extvalues wl =
    let tr_one acc w = match w.w_desc with
      | Wconst _ -> acc
      | _ -> (ivar_of_extvalue w)::acc
    in
      List.fold_left tr_one [] wl

  let read_extvalue funs acc w =
    (* recursive call *)
    let _, acc = Mls_mapfold.extvalue funs acc w in
    let acc =
      match w.w_desc with
        | Wconst _ -> acc
        | _ -> IvarSet.add (ivar_of_extvalue w) acc
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
      e, vars_ck acc e.e_ck

  let rec vars_pat acc = function
    | Evarpat x -> IvarSet.add (Ivar x) acc
    | Etuplepat pat_list -> List.fold_left vars_pat acc pat_list

  let def eq =
    vars_pat IvarSet.empty eq.eq_lhs

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

  let init f =
    (* build vds cache *)
    let build env vds =
      List.fold_left (fun env vd -> Env.add vd.v_ident vd env) env vds
    in
    let env = build Env.empty f.n_input in
    let env = build env f.n_output in
    let env = build env f.n_local in
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
        Tid (Modules.find_field f)

  let is_optimized_ty ty =
    match Modules.unalias_type ty with
      | Tarray _ -> true
      | Tid n ->
          (match Modules.find_type n with
            | Signature.Tstruct _ -> true
            | _ -> false)
      | _ -> false

  let is_optimized iv =
    is_optimized_ty (ivar_type iv)

  let is_memory x =
    IvarSet.mem (Ivar x) !memories

  let igs = ref []

  let node_for_ivar iv =
    let rec _node_for_ivar igs iv =
      match igs with
        | [] -> (*Format.eprintf "Var not in graph: %s\n" (ivar_to_string x); *) raise Not_found
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
  let igx, nodex = World.node_for_ivar x in
  let igy, nodey = World.node_for_ivar y in
    if igx == igy then
      f igx nodex nodey
    else
      def

let by_name def f x y =
  let igx, nodex = World.node_for_name x in
  let igy, nodey = World.node_for_name y in
    if igx == igy then
      f igx nodex nodey
    else
      def

let add_interference_link_from_name = by_name () add_interference_link
let add_interference_link_from_ivar = by_ivar () add_interference_link
let add_affinity_link_from_name = by_name () add_affinity_link
let add_affinity_link_from_ivar = by_ivar () add_affinity_link
let add_same_value_link_from_name = by_name () add_affinity_link
let add_same_value_link_from_ivar = by_ivar () add_affinity_link
let coalesce_from_name = by_name () coalesce
let have_same_value_from_name = by_name false have_same_value



(** Returns a map giving the number of uses of each ivar in the equations [eqs]. *)
let compute_uses eqs =
  let aux env eq =
    let incr_uses iv env =
      if IvarEnv.mem iv env then
        IvarEnv.add iv ((IvarEnv.find iv env) + 1) env
      else
        IvarEnv.add iv 1 env
    in
      IvarSet.fold incr_uses (InterfRead.read eq) env
  in
    List.fold_left aux IvarEnv.empty eqs

let number_uses iv uses =
  try
    IvarEnv.find iv uses
  with
    | Not_found -> 0

let add_uses uses iv env =
  if World.is_optimized iv then (
    Format.printf "Adding uses of %s@." (ivar_to_string iv);
    IvarEnv.add iv (number_uses iv uses) env
  ) else (
    Format.printf "Ignoring uses of %s@." (ivar_to_string iv);
    env
  )

let compute_live_vars eqs =
  let uses = compute_uses eqs in
  let aux (env,res) eq =
    let decr_uses iv env =
      if World.is_optimized iv then
        try
          IvarEnv.add iv ((IvarEnv.find iv env) - 1) env
        with
          | Not_found -> Format.printf "var not found : %s@." (ivar_to_string iv); assert false
      else
        env
    in
    let env = IvarSet.fold decr_uses (InterfRead.read eq) env in
    let alive_vars = IvarEnv.fold (fun iv n acc -> if n > 0 then iv::acc else acc) env [] in
    let res = (eq, alive_vars)::res in
    let env = IvarSet.fold (add_uses uses) (InterfRead.def eq) env in
      env, res
  in
  let env = IvarSet.fold (add_uses uses) !World.memories IvarEnv.empty in
  let _, res = List.fold_left aux (env, []) eqs in
    res


let rec disjoint_clock is_mem ck1 ck2 =
  match ck1, ck2 with
    | Cbase, Cbase -> false
    | Con(ck1, c1, n1), Con(ck2,c2,n2) ->
        if ck1 = ck2 & n1 = n2  & c1 <> c2 then
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
    let y_is_mem = World.is_memory y  in
    let are_copies = have_same_value_from_name x y in
    let disjoint_clocks = disjoint_clock (x_is_mem && y_is_mem) vdx.v_clock vdy.v_clock in
      not (disjoint_clocks or are_copies)
  )

let should_interfere = Misc.memoize_couple should_interfere

(** Builds the (empty) interference graphs corresponding to the
    variable declaration list vds. It just creates one graph per type
    and one node per declaration. *)
let init_interference_graph f =
  (** Adds a node to the list of nodes for the given type. *)
  let add_node env iv ty =
    let ty = Modules.unalias_type ty in
      if World.is_optimized_ty ty then
        TyEnv.add_element ty (mk_node iv) env
      else
        env
  in
  (** Adds a node for the variable and all fields of a variable. *)
  let rec add_ivar env iv ty =
    let env = add_node env iv ty in
    (match ty with
       | Tid n ->
         (try
            let fields = Modules.find_struct n in
              List.fold_left (fun env { f_name = f; f_type = ty } ->
                add_ivar env (Ifield (iv, f)) ty) env fields
          with
              Not_found -> env
         )
       | _ -> env
    )
  in
  (* do not add not linear inputs*)
  let vds = (*List.filter is_linear f.n_input @ *) f.n_output @ f.n_local in
  let env = List.fold_left
    (fun env vd -> add_ivar env (Ivar vd.v_ident) vd.v_type) TyEnv.empty vds in
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


(** @return whether [ty] corresponds to a record type. *)
let is_record_type ty = match ty with
  | Tid n ->
      (match Modules.find_type n with
        | Tstruct _ -> true
        | _ -> false)
  | _ -> false

(** [filter_vars l] returns a list of variables whose fields appear in
    a list of ivar.*)
let rec filter_fields = function
  | [] -> []
  | (Ifield (id, _))::l -> id::(filter_fields l)
  | _::l -> filter_fields l

(** Returns all the fields of a variable (when it corresponds to a record). *)
let rec record_vars acc iv ty =
  let acc = iv::acc in
  match ty with
    | Tid n ->
        (try
            let fields = Modules.find_struct n in
              List.fold_left (fun acc { f_name = n; f_type = ty } ->
                record_vars acc (Ifield(iv, n)) ty) acc fields
          with
              Not_found -> acc
        )
    | _ -> acc

(** Adds all fields of a var in the list of live variables of
    every equation. If x is live in eq, then so are all x.f. *)
let fix_records_live_vars live_vars =
  let fix_one_list vars =
    List.fold_left (fun acc iv -> record_vars acc iv (World.ivar_type iv)) [] vars
  in
    List.map (fun (eq, vars) -> eq, fix_one_list vars) live_vars

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



(** [process_eq igs eq] adds to the interference graphs igs
    the links corresponding to the equation. Interferences
    corresponding to live vars sets are already added by build_interf_graph.
*)
let process_eq ({ eq_lhs = pat; eq_rhs = e } as eq) =
  (** Other cases*)
  match pat, e.e_desc with
  (*  | Eapp ({ a_op = (Efun f | Enode f) }, e_list, _) ->
      let targeting = (find_value f).node_targeting in
        apply_targeting igs targeting e_list pat eq *)
    | _, Eiterator(Imap, { a_op = Enode _ | Efun _ }, _, _, w_list, _) ->
      let invars = InterfRead.ivars_of_extvalues w_list in
      let outvars = IvarSet.elements (InterfRead.def eq) in
        List.iter (fun inv -> List.iter
          (add_affinity_link_from_ivar inv) outvars) invars
    | Evarpat x, Efby(_, w) -> (* x  = _ fby y *)
        (match w.w_desc with
          | Wconst _ -> ()
          | _ -> add_affinity_link_from_ivar (InterfRead.ivar_of_extvalue w) (Ivar x) )
    | Evarpat x, Eextvalue w ->
      (* Add links between variables with the same value *)
        (match w.w_desc with
          | Wconst _ -> ()
          | _ ->  add_same_value_link_from_ivar (InterfRead.ivar_of_extvalue w) (Ivar x) )
    | _ -> () (* do nothing *)

(** Add the special init and return equations to the dependency graph
    (resp at the bottom and top) *)
let add_init_return_eq f =
   (** a_1,..,a_p = __init__  *)
  let eq_init = mk_equation (Mls_utils.pat_from_dec_list f.n_input)
    (mk_extvalue_exp Initial.tint (Wconst (Initial.mk_static_int 0))) in
    (** __return__ = o_1,..,o_q *)
  let eq_return = mk_equation (Etuplepat [])
    (mk_exp Tinvalid (Mls_utils.tuple_from_dec_list f.n_output)) in
    (eq_init::f.n_equs)@[eq_return]


let build_interf_graph f =
  World.init f;
  (** Init interference graph *)
  init_interference_graph f;

  let eqs = add_init_return_eq f in
  (** Build live vars sets for each equation *)
  let live_vars = compute_live_vars eqs in
    (* Coalesce linear variables *)
    (*coalesce_linear_vars igs vds;*)
    (** Other cases*)
    List.iter process_eq f.n_equs;
    (* Make sure the interference between records are coherent *)
    let live_vars = fix_records_live_vars live_vars in
    (* Add interferences from live vars set*)
    add_interferences live_vars;
    (* Add interferences between records implied by IField values*)
    add_records_field_interferences ();

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
    List.iter color record_igs;
    (* Then update fields colors *)
    List.iter color_fields igs;
    (* and finish the coloring *)
    List.iter color igs

let print_graphs f igs =
  let cpt = ref 0 in
  let print_graph ig =
    let s = (Names.shortname f.n_name)^ (string_of_int !cpt) in
      print_graph (Names.fullname f.n_name) s ig;
      cpt := !cpt + 1
  in
    List.iter print_graph igs

(** Create the list of lists of variables stored together,
    from the interference graph.*)
let create_subst_lists igs =
  let create_one_ig ig =
    List.map (fun x -> ig.g_type, x) (values_by_color ig)
  in
    List.flatten (List.map create_one_ig igs)

let node _ acc f =
  (** Build the interference graphs *)
  let igs = build_interf_graph f in
    (** Color the graph *)
    color_interf_graphs igs;
    if memalloc_debug then
      print_graphs f igs;
    (** Remember the choice we made for code generation *)
      { f with n_mem_alloc = create_subst_lists igs }, acc

let program p =
  let funs = { Mls_mapfold.defaults with Mls_mapfold.node_dec = node } in
  let p, _ = Mls_mapfold.program_it funs () p in
    p
