(** A scheduler that tries to minimize interference between variables, in
    order to have a more efficient memory allocation. *)
open Idents
open Minils
open Mls_utils
open Misc
open Sgraph

module EqMap =
  Map.Make (
    struct type t = eq
           let compare = compare
    end)

let eq_clock eq =
  eq.eq_rhs.e_base_ck

module Cost =
struct
  open Interference_graph
  open Interference

  (** Returns the minimum of the values in the map.
      Picks an equation with the clock ck if possible. *)
  let min_map ck m =
    let one_min k d (v,eq,same_ck) =
      match eq with
        | None -> (d, Some k, eq_clock k = ck)
        | Some eq ->
          if d < v then
            (d, Some k, eq_clock eq = ck)
          else if d = v & not same_ck & eq_clock eq = ck then
            (v, Some k, true)
          else
            (v, Some eq, same_ck)
    in
    let _, eq, _ = EqMap.fold one_min m (0, None, false) in
      match eq with
        | None -> assert false
        | Some eq -> eq

  (** Remove from the elements the elements whose value is zero or negative. *)
  let remove_null m =
    let check_not_null k d m =
      if d > 0 then IvarEnv.add k d m else m
    in
      IvarEnv.fold check_not_null m IvarEnv.empty

  (** Returns the list of variables killed by an equation (ie vars
      used by the equation and with use count equal to 1). *)
  let killed_vars eq env =
    let is_killed iv acc =
      try
        if IvarEnv.find iv env = 1 then acc + 1 else acc
      with
        | Not_found ->
          Format.printf "Var not found in kill_vars %s@." (ivar_to_string iv); assert false
    in
      IvarSet.fold is_killed (all_ivars_set (InterfRead.read eq)) 0

  (** Compute the cost of all the equations in rem_eqs using var_uses.
      So far, it uses only the number of killed and defined variables. *)
  let compute_costs env rem_eqs =
    let cost eq =
      let nb_killed_vars = killed_vars eq env in
      let nb_def_vars = IvarSet.cardinal (all_ivars_set (InterfRead.def eq)) in
        nb_def_vars - nb_killed_vars
    in
      List.fold_left (fun m eq -> EqMap.add eq (cost eq) m) EqMap.empty rem_eqs

  (** Initialize the costs data structure. *)
  let init_cost uses inputs =
    let env = IvarSet.fold (add_uses uses) !World.memories IvarEnv.empty in
    let inputs = List.map (fun vd -> Ivar vd.v_ident) inputs in
      List.fold_left (fun env iv -> add_uses uses iv env) env inputs

  (** [update_cost eq uses env] updates the costs data structure
      after eq has been chosen as the next equation to be scheduled.
      It updates uses and adds the new variables defined by this equation.
  *)
  let update_cost eq uses env =
    let env = IvarSet.fold decr_uses (all_ivars_set (InterfRead.read eq)) env in
      IvarSet.fold (add_uses uses) (InterfRead.def eq) env

  (** Returns the next equation, chosen from the list of equations rem_eqs *)
  let next_equation rem_eqs ck env =
    let eq_cost = compute_costs env rem_eqs in
      min_map ck eq_cost
end

(** Returns the list of 'free' nodes in the dependency graph (nodes without
    predecessors). *)
let free_eqs node_list =
  let is_free n =
    (List.length n.g_depends_on) = 0
  in
    List.map (fun n -> n.g_containt) (List.filter is_free node_list)

let rec node_for_eq eq nodes_list =
  match nodes_list with
    | [] -> raise Not_found
    | n::nodes_list ->
      if eq = n.g_containt then
        n
      else
        node_for_eq eq nodes_list

(** Remove an equation from the dependency graph. All the edges to
    other nodes are removed. *)
let remove_eq eq node_list =
  let n = node_for_eq eq node_list in
    List.iter (remove_depends n) n.g_depends_on;
    List.iter (fun n2 -> remove_depends n2 n) n.g_depends_by;
    List.filter (fun n2 -> n.g_tag <> n2.g_tag) node_list

(** Main function to schedule a node. *)
let schedule eq_list inputs node_list =
  let uses = Interference.compute_uses eq_list in
  let rec schedule_aux rem_eqs sched_eqs node_list ck costs =
    match rem_eqs with
      | [] -> sched_eqs
      | _ ->
        (* First choose the next equation to schedule depending on costs*)
        let eq = Cost.next_equation rem_eqs ck costs in
        (* remove it from the dependency graph *)
        let node_list = remove_eq eq node_list in
        (* update the list of equations ready to be scheduled *)
        let rem_eqs = free_eqs node_list in
        (* compute new costs for the next step *)
        let costs = Cost.update_cost eq uses costs in
          schedule_aux rem_eqs (eq::sched_eqs) node_list (eq_clock eq) costs
  in
  let costs = Cost.init_cost uses inputs in
  let rem_eqs = free_eqs node_list in
    List.rev (schedule_aux rem_eqs [] node_list Clocks.Cbase costs)

let schedule_contract c =
  c

let node _ () f =
  Interference.World.init f;
  let contract = optional schedule_contract f.n_contract in
  let node_list, _ = DataFlowDep.build f.n_equs in
  let f = { f with n_equs = schedule f.n_equs f.n_input node_list; n_contract = contract } in
    f, ()

let program p =
  let funs = { Mls_mapfold.defaults with Mls_mapfold.node_dec = node } in
  let p, () = Mls_mapfold.program_it funs () p in
    p
