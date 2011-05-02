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
  eq.eq_rhs.e_ck

module Cost =
struct
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
      if d > 0 then Env.add k d m else m
    in
      Env.fold check_not_null m Env.empty

  (** [remove_uses l m] decrease by one the value in the map m of each element
      in the list l. This corresponds to removing one use for each variable. *)
  let remove_uses l m =
    let remove_one_use k d m =
      if (List.mem k l) & (d - 1 > 0) then
        Env.add k (d-1) m
      else
        m
    in
      Env.fold remove_one_use m m

  (** Returns the list of variables killed by an equation (ie vars
      used by the equation and with use count equal to 1). *)
  let killed_vars eq var_uses =
    let is_killed acc v =
      begin try
              if Env.find v var_uses = 1 then
                acc + 1
              else
                acc
        with Not_found ->
          Format.printf "not found variable : %s" (name v); assert false
      end
    in
      List.fold_left is_killed 0 (Vars.read false eq)

  (** [uses x eq_list] returns the number of uses of the variable x
      in the lits of equations eq_list. *)
  let uses x eq_list =
    let appears_in_eq x eq =
      if List.mem x (Vars.read false eq) then
        1
      else
        0
  in
    List.fold_left (fun v eq -> (appears_in_eq x eq) + v) 0 eq_list

  (** Adds variables from the list l to the map m.
      eq_list is used to compute the initial number of uses of this variable. *)
  let add_vars l eq_list m =
    List.fold_left (fun m v -> Env.add v (uses v eq_list) m) m l

  (** Compute the cost of all the equations in rem_eqs using var_uses.
      So far, it uses only the number of killed and defined variables. *)
  let compute_costs var_uses rem_eqs =
    let cost eq =
      let nb_killed_vars = killed_vars eq var_uses in
      let nb_def_vars = List.length (Vars.def [] eq) in
        nb_def_vars - nb_killed_vars
    in
      List.fold_left (fun m eq -> EqMap.add eq (cost eq) m) EqMap.empty rem_eqs

  (** Initialize the costs data structure. *)
  let init_cost eq_list inputs =
    add_vars inputs eq_list Env.empty

  (** [update_cost eq eq_list var_uses] updates the costs data structure
      after eq has been chosen as the next equation to be scheduled.
      It updates uses and adds the new variables defined by this equation.
  *)
  let update_cost eq eq_list var_uses =
    let var_uses = remove_uses (Vars.read false eq) var_uses in
      add_vars (Vars.def [] eq) eq_list var_uses

  (** Returns the next equation, chosen from the list of equations rem_eqs *)
  let next_equation rem_eqs ck var_uses =
    let eq_cost = compute_costs var_uses rem_eqs in
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
        let costs = Cost.update_cost eq eq_list costs in
          schedule_aux rem_eqs (eq::sched_eqs) node_list (eq_clock eq) costs
  in
  let costs = Cost.init_cost eq_list inputs in
  let rem_eqs = free_eqs node_list in
    List.rev (schedule_aux rem_eqs [] node_list Clocks.Cbase costs)

let schedule_contract c =
  c

let node _ () f =
  let contract = optional schedule_contract f.n_contract in
  let inputs = List.map (fun vd -> vd.v_ident) (f.n_input@f.n_local) in
  let node_list, _ = DataFlowDep.build f.n_equs in
  let f = { f with n_equs = schedule f.n_equs inputs node_list; n_contract = contract } in
    f, ()

let program p =
  let funs = { Mls_mapfold.defaults with Mls_mapfold.node_dec = node } in
  let p, () = Mls_mapfold.program_it funs () p in
    p
