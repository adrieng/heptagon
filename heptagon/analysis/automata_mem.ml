open Ident
open Names
open Heptagon
open Interference_graph

let node_for_name s g =
  try
    node_for_value g s
  with
      Not_found -> 
	let n = mk_node s in
	  add_node g n;
	  n

let find_reset_jumps g sh =
  let reset_escape state esc =
    if esc.e_reset = true then 
      ( Format.printf "Jump from %s to %s with reset\n" state esc.e_next_state;
	let n1 = node_for_name state g in
	let n2 = node_for_name esc.e_next_state g in
	  add_interference_link n1 n2
      ) else
      (Format.printf "Jump from %s to %s is not resetted\n" state esc.e_next_state;
      	let n1 = node_for_name state g in
	let n2 = node_for_name esc.e_next_state g in
	  add_affinity_link n1 n2
      )
  in
    List.iter (reset_escape sh.s_state) sh.s_until

let share_eq g eq =
  match eq.eq_desc with
    | Eautomaton sh_list ->
	List.iter (find_reset_jumps g) sh_list
    | _ -> Format.printf "Ignoring unsupported eq\n"

let node f =
  let g = mk_graph [] f.n_name in
    List.iter (share_eq g) f.n_equs;
    { f with n_states_graph = g; }

let program p =
  { p with p_nodes = List.map node p.p_nodes }
