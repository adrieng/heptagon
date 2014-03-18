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
(** A scheduler that tries to minimize interference between variables, in
    order to have a more efficient memory allocation. *)
open Idents
open Minils
open Mls_utils
open Sgraph

(** In order to put together equations with the same control structure, we have to take into
    account merge equations, that will to be translated to two instructions on slow clocks
    although the activation clock of the equation is fast. *)
let control_ck eq =
  match eq.eq_rhs.e_desc with
    | Emerge (_, (_, w)::_) ->  w.w_ck
    | _ -> Mls_utils.Vars.clock eq

(** Returns a map giving the number of uses of each ivar in the equations [eqs]. *)
let compute_uses eqs =
  let aux env eq =
    let incr_uses env x =
      if Env.mem x env then
        Env.add x ((Env.find x env) + 1) env
      else
        Env.add x 1 env
    in
    let reads = Mls_utils.Vars.read false eq in
    (* self uses not counted *)
    let defs = Mls_utils.Vars.def [] eq in
    let reads =
      List.fold_left
	(fun acc x -> if List.mem x defs then acc else (x::acc))
	[] reads in
    List.fold_left incr_uses env reads
  in
  List.fold_left aux Env.empty eqs

let number_uses x uses =
  try
    Env.find x uses
  with
    | Not_found -> 0
        (* add one use for memories without any use to make sure they interfere
           with other memories and outputs. *)
        (*if Interference.World.is_memory x then 1 else 0*)



module Cost =
struct
  open Interference
  open Interference_graph

  (* Care only for optimized variables (arrays) *)
  let filter_opt x_l =
    List.filter (fun x -> World.is_optimized (Ivar x)) x_l

  (** Care only for optimized variables (arrays) *)
  let read_opt eq =
    let reads = Mls_utils.Vars.read false eq in
    filter_opt reads

  (** Care only for optimized variables (arrays) *)
  let def_opt eq =
    let defs = Mls_utils.Vars.def [] eq in
    filter_opt defs

  let add_uses uses env x =
    Interference.print_debug
      "Adding %d uses for %a@." (number_uses x uses) print_ident x;
    Env.add x (number_uses x uses) env

  let decr_uses env x =
    try
      Env.add x ((Env.find x env) - 1) env
    with Not_found -> (* Self use: no decrease for x *) env


  (** Remove from the elements the elements whose value is zero or negative. *)
  let remove_null m =
    let check_not_null k d m =
      if d > 0 then Env.add k d m else m
    in
      Env.fold check_not_null m Env.empty

  (** Returns the list of variables killed by an equation (ie vars
      used by the equation and with use count equal to 1). *)
  let killed_vars eq env =
    let is_killed acc x =
      try
        if Env.find x env = 1 then acc + 1 else acc
      with
        | Not_found ->
	    (* self use of x *)
	    acc
    in
    List.fold_left is_killed 0 (read_opt eq)

  (** Initialize the costs data structure. *)
  let init_cost uses inputs =
    print_debug "Init cost@.";
    let mem_opt =
      IdentSet.filter (fun x -> World.is_optimized (Ivar x)) !World.memories
    in
    let env =
      IdentSet.fold (fun x env -> add_uses uses env x) mem_opt Env.empty
    in
    let inputs = filter_opt (List.map (fun vd -> vd.v_ident) inputs) in
    List.fold_left (add_uses uses) env inputs

  (** [update_cost eq uses env] updates the costs data structure
      after eq has been chosen as the next equation to be scheduled.
      It updates uses and adds the new variables defined by this equation.
  *)
  let update_cost eq uses env =
    let env = List.fold_left decr_uses env (read_opt eq) in
      List.fold_left (add_uses uses) env (def_opt eq)

  (** Returns the next equation, chosen from the list of equations rem_eqs *)
  let next_equation rem_eqs ck env =
    let bonus eq = match eq.eq_rhs.e_desc with
      | Eapp ({a_op = (Eupdate | Efield_update) },_,_) -> 1
      | Efby _ -> 20
      | _ -> 0
    in
    let cost eq =
      let nb_killed_vars = killed_vars eq env in
      let nb_def_vars = List.length (def_opt eq) in
      let b = bonus eq in
      print_debug "(%d,%d,%d)%a@."
        nb_killed_vars nb_def_vars b Mls_printer.print_eq eq;
      nb_def_vars - nb_killed_vars + b

    in
    (* returns the minimum element of the list with same_ctrl = true if possible. *)
    let rec min_same_ck (min_eq, min_c, min_same_ctrl) l = match l with
      | [] -> min_eq
      | (eq, c, same_ctrl)::l ->
          if (c < min_c) || (c = min_c && (same_ctrl && not min_same_ctrl)) then
            min_same_ck (eq, c, same_ctrl) l
          else
            min_same_ck (min_eq, min_c, min_same_ctrl) l
    in
    let eqs_wcost =
      List.map
        (fun eq -> (eq, cost eq, Clocks.same_control (control_ck eq) ck))
        rem_eqs
    in
    let (eq, c, same_ctrl), eqs_wcost = Misc.assert_1min eqs_wcost in
    min_same_ck (eq, c, same_ctrl) eqs_wcost
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
  (* Compute number of uses of each ident *)
  let uses = compute_uses eq_list in
  let rec schedule_aux rem_eqs sched_eqs node_list ck costs =
    match rem_eqs with
      | [] ->
        if List.length node_list <> 0 then
          Misc.internal_error "Node is unschedulable";
        sched_eqs
      | _ ->
        (* First choose the next equation to schedule depending on costs*)
        let eq = Cost.next_equation rem_eqs ck costs in
        (* remove it from the dependency graph *)
        let node_list = remove_eq eq node_list in
        (* update the list of equations ready to be scheduled *)
        let rem_eqs = free_eqs node_list in
        (* compute new costs for the next step *)
        let costs = Cost.update_cost eq uses costs in
        schedule_aux rem_eqs (eq::sched_eqs) node_list (control_ck eq) costs
  in
  let costs = Cost.init_cost uses inputs in
  let rem_eqs = free_eqs node_list in
    List.rev (schedule_aux rem_eqs [] node_list Clocks.Cbase costs)

let schedule_contract contract c_inputs =
  match contract with
    None -> None, []
  | Some c ->
      let node_list, _ = DataFlowDep.build c.c_eq in
      (Some { c with c_eq = schedule c.c_eq c_inputs node_list; }),
      c.c_controllables

let node _ () f =
  (* Put memory variables into Interference.World.memories *)
  Interference.World.init f;
  (* Schedule contract *)
  let contract,controllables = schedule_contract f.n_contract (f.n_input@f.n_output) in
  (* Build dataflow dependency graph *)
  let node_list, _ = DataFlowDep.build f.n_equs in
  (* Controllable variables are considered as inputs *)
  let f = { f with
              n_equs = schedule f.n_equs (f.n_input@controllables) node_list;
              n_contract = contract } in
    f, ()

let program p =
  let m = !Compiler_options.interf_all in
  Compiler_options.interf_all := false;
  let funs = { Mls_mapfold.defaults with Mls_mapfold.node_dec = node } in
  let p, () = Mls_mapfold.program_it funs () p in
  Compiler_options.interf_all := m;
  p
