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
open Idents
open Types
open Signature
open Clocks
open Minils
open Linearity
open Interference_graph
open Containers

let print_interference_graphs = false
let verbose_mode = false

module TyEnv =
    ListMap(struct
      type t = ty
      let compare = Global_compare.type_compare
    end)

module VarEnv = struct
  include Idents.Env

  let add_ivar env iv =
    let x = var_ident_of_ivar iv in
    if mem x env then
      add x (IvarSet.add iv (find x env)) env
    else
      add x (IvarSet.singleton iv) env

  let remove_except_mem x env =
    if mem x env then (
      let s = IvarSet.filter is_mem_ivar (find x env) in
      if IvarSet.is_empty s then
        remove x env
      else
        add x s env
    ) else env
end

let print_debug fmt =
  if verbose_mode then
    Format.printf fmt
  else
    Format.ifprintf Format.std_formatter fmt

let print_debug_ivar_env name env =
  if verbose_mode then (
    Format.printf "%s:  " name;
    IvarEnv.iter (fun k v -> Format.printf "%a : %d; " print_ivar k v) env;
    Format.printf "@."
  )

let print_debug_var_env name env =
  if verbose_mode then (
    Format.printf "%s:  " name;
    VarEnv.iter (fun _ l -> IvarSet.iter (fun k -> Format.printf "%a; " print_ivar k) l) env;
    Format.printf "@."
  )

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
    | Clocks.Con(ck2, _, n) -> (Ivar n)::(vars_ck acc ck2)
    | Clocks.Cbase | Cvar { contents = Cindex _ } -> acc
    | Cvar { contents = Clink ck } -> vars_ck acc ck

  let rec vars_ct acc ct = match ct with
    | Ck ck -> vars_ck acc ck
    | Cprod ct_list -> List.fold_left vars_ct acc ct_list

  let rec ivar_of_extvalue w' = match w'.w_desc with
    | Wvar x -> Ivar x
    | Wfield(w, f) -> Ifield (ivar_of_extvalue w, f)
    | Wwhen(w, _, _) -> Iwhen (ivar_of_extvalue w, w'.w_ck)
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

  let read_extvalue _ acc w =
    (* recursive call *)
    (*let _, acc = Mls_mapfold.extvalue funs acc w in*)
    let acc =
      try
        (ivar_of_extvalue w)::acc
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
      | Eiterator (_, _, _, _, _, Some x) -> (Ivar x)::acc
      | _ -> acc
    in
      e, acc

  let rec vars_pat acc = function
    | Evarpat x -> x::acc
    | Etuplepat pat_list -> List.fold_left vars_pat acc pat_list

  let def eq =
    vars_pat [] eq.eq_lhs
  let def_ivars eq =
    List.map (fun x -> Ivar x) (def eq)

  let rec nth_var_from_pat j pat =
    match j, pat with
      | 0, Evarpat x -> x
      | n, Etuplepat l -> nth_var_from_pat 0 (List.nth l n)
      | _, _ -> assert false

  let read_exp e =
    let funs = { Mls_mapfold.defaults with
      Mls_mapfold.exp = read_exp;
      Mls_mapfold.extvalue = read_extvalue } in
    let _, acc =  Mls_mapfold.exp_it funs [] e in
      acc

  let read eq =
    read_exp eq.eq_rhs
end


module World = struct
  let vds = ref Env.empty
  let memories = ref IdentSet.empty
  let igs = ref []

  let init f =
    (* build vds cache *)
    let build env vds =
      List.fold_left (fun env vd -> Env.add vd.v_ident vd env) env vds
    in
    let env = build Env.empty f.n_input in
    let env = build env f.n_output in
    let env = build env f.n_local in
    let env =
      match f.n_contract with
        None -> env
      | Some c ->
          let env = build env c.c_local in
          build env c.c_controllables in
      igs := [];
      vds := env;
      (* build the set of memories *)
      let mems = Mls_utils.node_memory_vars f in
      let s = List.fold_left (fun s (x, _) -> IdentSet.add x s) IdentSet.empty mems in
      memories := s

  let vd_from_ident x =
    try Env.find x !vds
    with Not_found ->
      Format.eprintf "Unknown variable %a@." print_ident x;
      Misc.internal_error "interference"

  let rec ivar_type iv = match iv with
    | Ivar x | Imem x ->
        let vd = vd_from_ident x in
          vd.v_type
    | Ifield(_, f) ->
        let n = Modules.find_field f in
        let fields = Modules.find_struct n in
          Signature.field_assoc f fields
    | Iwhen (iv, _) -> ivar_type iv

  let ivar_clock iv = match iv with
    | Iwhen (_, ck) -> ck
    | _ ->
        let vd = vd_from_ident (var_ident_of_ivar iv) in
        vd.v_clock

  let is_optimized_ty ty =
    (!Compiler_options.interf_all (* && not (is_enum ty)) *) ) || is_array_or_struct ty

  let is_optimized iv =
    is_optimized_ty (ivar_type iv)

  let is_memory x =
    IdentSet.mem x !memories

  let node_for_ivar iv =
    let rec _node_for_ivar igs iv =
      match igs with
        | [] -> print_debug "Var not in graph: %a@." print_ivar iv; raise Not_found
        | ig::igs ->
            (try
                ig, node_for_value ig iv
              with Not_found ->
                _node_for_ivar igs iv)
    in
      _node_for_ivar !igs (remove_iwhen  iv)

  let node_for_name x =
    node_for_ivar (Ivar x)
end

(** Helper functions to work with the multiple interference graphs *)

let by_ivar def f x y =
  if World.is_optimized x && World.is_optimized y then (
    let igx, nodex = World.node_for_ivar x in
    let igy, nodey = World.node_for_ivar y in
      if igx == igy then
        f igx nodex nodey
      else
        def
  ) else
    def

let by_name def f x y =
  if World.is_optimized (Ivar x) && World.is_optimized (Ivar y) then (
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
let have_same_value_from_ivar = by_ivar false have_same_value

let remove_from_ivar iv =
  try
    let ig, v = World.node_for_ivar iv in
      G.remove_vertex ig.g_graph v
  with
    | Not_found -> (* var not in graph, just ignore it *) ()


(** Adds all the fields of a variable to the list [l] (when it corresponds to a record). *)
let rec all_ivars l iv ck ty =
  if not (World.is_optimized_ty ty) then
    l
  else (
    let iv' = match ck with None -> iv | Some ck -> Iwhen(iv, ck) in
    let l = iv'::l in
    match Modules.unalias_type ty with
      | Tid n ->
          (try
              let fields = Modules.find_struct n in
              List.fold_left (all_ivars_field iv ck) l fields
            with
                Not_found -> l
          )
      | _ -> l
  )

and all_ivars_field iv ck l { f_name = n; f_type = ty } =
  let new_iv = match ck with
    | None -> Ifield(iv, n)
    | Some ck -> Iwhen (Ifield(iv, n), ck)
  in
  all_ivars l new_iv ck ty

let all_ivars_list ivs =
  let add_one acc iv =
    let ck = match iv with
      | Iwhen (_, ck) -> Some ck
      | _ -> None
    in
    let iv = remove_iwhen iv in
    all_ivars acc iv ck (World.ivar_type iv)
  in
  List.fold_left add_one [] ivs

let is_fast_memory x =
  match ck_repr (World.ivar_clock (Imem x)) with
    | Clocks.Cbase -> false
    | _ -> true

(* TODO: variables with no use ?? *)
let compute_live_vars eqs =
  let aux (alive_vars, res) eq =
    let read_ivars = all_ivars_list (InterfRead.read eq) in
    let def_ivars = InterfRead.def eq in
    (* add vars used in the equation *)
    let alive_vars = List.fold_left VarEnv.add_ivar alive_vars read_ivars in
    (* remove vars defined in this equation *)
    let alive_vars =
      List.fold_left (fun alive_vars id -> VarEnv.remove_except_mem id alive_vars)
                     alive_vars
                     def_ivars
    in
    print_debug "%a@," Mls_printer.print_eq eq;
    print_debug_var_env "alive" alive_vars;
    let alive_vars_list = VarEnv.fold (fun _ ivs acc -> (IvarSet.elements ivs)@acc) alive_vars [] in
    let res = (eq, alive_vars_list)::res in
    alive_vars, res
  in
  let add_mem x env =
    if is_fast_memory x then VarEnv.add_ivar env (Imem x) else env
  in
  (* Adds all ivars representing memories *)
  let env = IdentSet.fold add_mem !World.memories VarEnv.empty in
  let _, res =  List.fold_left aux (env, []) (List.rev eqs) in
    res

(** [should_interfere x y] returns whether variables x and y
    can interfere. *)
let should_interfere (ivx, ivy) =
  let tyx = World.ivar_type ivx in
  let tyy = World.ivar_type ivy in
  if Global_compare.type_compare tyx tyy <> 0 then
    false
  else (
    match ivx, ivy with
      | Imem _, Imem _ ->
        let ckx = World.ivar_clock ivx in
        let cky = World.ivar_clock ivy in
        Global_compare.clock_compare ckx cky <> 0
      | Imem x, iv | iv, Imem x ->
        let ckx = World.ivar_clock (Imem x) in
        let ck = World.ivar_clock iv in
        not (Clocks.is_subclock ck ckx)
      | _, _ ->
        let x_is_mem = World.is_memory (var_ident_of_ivar ivx) in
        let x_is_when = is_when_ivar ivx in
        let y_is_mem = World.is_memory (var_ident_of_ivar ivy) in
        let y_is_when = is_when_ivar ivy in
        let ckx = World.ivar_clock ivx in
        let cky = World.ivar_clock ivy in
        let are_copies = have_same_value_from_ivar ivx ivy in
        (* a register with a slow clock is still alive even when it is not activated.
           However, if we read a fast register on a slow rhythm,
           we can share it with other variables on disjoint slow rhythms as we know
           that the value of the register will
           be done at the end of the step. *)
        let disjoint_clocks =
          not ((x_is_mem && not x_is_when) ||
                  (y_is_mem && not y_is_when)) && Clocks.are_disjoint ckx cky
        in
        not (disjoint_clocks || are_copies)
  )

let should_interfere = Misc.memoize_couple should_interfere


(** Builds the (empty) interference graphs corresponding to the
    variable declaration list vds. It just creates one graph per type
    and one node per declaration. *)
let init_interference_graph () =
  let add_tyenv env iv =
    let ty = Static.simplify_type Names.QualEnv.empty (World.ivar_type iv) in
    TyEnv.add_element ty (Interference_graph.mk_node iv) env
  in
  (* Adds a node for the variable and all fields of a variable. *)
  let add_ivar env iv ty =
    let ivars = all_ivars [] iv None ty in
      List.fold_left add_tyenv env ivars
  in
  let env = Env.fold
    (fun _ vd env -> add_ivar env (Ivar vd.v_ident) vd.v_type) !World.vds TyEnv.empty in
  (* add special nodes for fast memories *)
  let env =
    IdentSet.fold
      (fun x env -> if is_fast_memory x then add_tyenv env (Imem x) else env)
      !World.memories env
  in
  World.igs := TyEnv.fold (fun ty l acc -> (mk_graph l ty)::acc) env []


(** Adds interferences between all the variables in
    the list. If force is true, then interference is added
    whatever the variables are, without checking if interference
    is real. *)
let add_interferences_from_list force vars =
  let add_interference ivx ivy =
    if force || should_interfere (ivx, ivy) then
      add_interference_link_from_ivar ivx ivy
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
  let spilled_inp = List.map (fun vd -> Ivar vd.v_ident) spilled_inp in
  let spilled_inp = all_ivars_list spilled_inp in
    List.iter remove_from_ivar spilled_inp

(** If we optimize all types, we need to spill outputs and memories so
    that register allocation by the C compiler is not disturbed. *)
let spill_mems_outputs f =
  let add_output l vd =
    if not (is_array_or_struct vd.v_type) then (Ivar vd.v_ident)::l else l
  in
  let add_memory x l =
    let iv = Ivar x in
    if not (is_array_or_struct (World.ivar_type iv)) then iv::l else l
  in
  let spilled_vars = List.fold_left add_output [] f.n_output in
  let spilled_vars = IdentSet.fold add_memory !World.memories spilled_vars in
  let spilled_vars = all_ivars_list spilled_vars in
  List.iter remove_from_ivar spilled_vars

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
  (* Other cases*)
  match pat, e.e_desc with
    | _, Eiterator((Imap|Imapi), { a_op = Enode _ | Efun _ }, _, pw_list, w_list, _) ->
      let invars = InterfRead.ivars_of_extvalues w_list in
      let pinvars = InterfRead.ivars_of_extvalues pw_list in
      let outvars = InterfRead.def_ivars eq in
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
    | Evarpat x, Eapp({ a_op = Eupdate }, args, _) ->
      let w, _ = Misc.assert_1min args in
      (try
          add_affinity_link_from_ivar (InterfRead.ivar_of_extvalue w) (Ivar x)
       with
         | InterfRead.Const_extvalue -> ())
    | Evarpat x, Eapp({ a_op = Efield_update }, args, _) ->
        let w1, w2 = Misc.assert_2 args in
        (* if we generate code for o = { a with .f = b } that is:
           o=a; o.f = b
           then we need to make sure that b interferes with all fields of o *)
        if !Compiler_options.memcpy_array_and_struct then
          (try
              let all_iv = all_ivars [] (Ivar x) None w1.w_ty in
              let iv2 = InterfRead.ivar_of_extvalue w2 in
              List.iter (add_interference_link_from_ivar iv2) all_iv;
            with
              | InterfRead.Const_extvalue -> ());
      (try
          let iv1 = InterfRead.ivar_of_extvalue w1 in
          add_affinity_link_from_ivar iv1 (Ivar x)
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
  let pat_from_dec_list decs =
    Etuplepat (List.map (fun vd -> Evarpat vd.v_ident) decs)
  in

  let tuple_from_dec_and_mem_list decs =
    let exp_of_vd vd =
      mk_extvalue ~clock:vd.v_clock ~ty:vd.v_type ~linearity:vd.v_linearity (Wvar vd.v_ident)
    in
    let exp_of_mem x = exp_of_vd (World.vd_from_ident x) in
    let decs = List.map exp_of_vd decs in
    let mems = IdentSet.fold (fun iv acc -> (exp_of_mem iv)::acc) !World.memories [] in
    Eapp(mk_app Earray, decs@mems, None)
  in

  (* a_1,..,a_p = __init__  *)
  let eq_init =
    mk_equation false
                (pat_from_dec_list f.n_input)
                (mk_extvalue_exp Clocks.Cbase
                                 Initial.tint
                                 ~linearity:Ltop
                                 (Wconst (Initial.mk_static_int 0))) in
  (* __return__ = o_1,..,o_q, mem_1, ..., mem_k *)
  let eq_return = mk_equation false (Etuplepat [])
    (mk_exp Clocks.Cbase Tinvalid ~linearity:Ltop (tuple_from_dec_and_mem_list f.n_output)) in
    (eq_init::f.n_equs)@[eq_return]

(** Coalesce Imem x and Ivar x *)
let coalesce_mems () =
  let coalesce_mem x =
    if is_fast_memory x then coalesce_from_ivar (Imem x) (Ivar x)
  in
  IdentSet.iter coalesce_mem !World.memories

let build_interf_graph f =
  World.init f;
  (* Init interference graph *)
  init_interference_graph ();

  let eqs = add_init_return_eq f in
  (* Build live vars sets for each equation *)
  let live_vars = compute_live_vars eqs in
    (* Coalesce linear variables *)
    coalesce_linear_vars ();
    (* Other cases *)
    List.iter process_eq f.n_equs;
    (* Add interferences from live vars set*)
    add_interferences live_vars;
    (* Add interferences between records implied by IField values*)
    add_records_field_interferences ();
    (* Coalesce all Imem x and Ivar x *)
    coalesce_mems ();
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
  (* Build the interference graphs *)
  let igs = build_interf_graph f in
    (* Color the graph *)
    color_interf_graphs igs;
    if print_interference_graphs then
      print_graphs f igs;
    (* Remember the choice we made for code generation *)
      { f with n_mem_alloc = create_subst_lists igs }, acc

let program p =
  let funs = { Mls_mapfold.defaults with Mls_mapfold.node_dec = node } in
  let p, _ = Mls_mapfold.program_it funs () p in
    p
