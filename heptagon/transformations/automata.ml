(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* removing automata statements *)

(* $Id$ *)

open Location
open Misc
open Names
open Ident
open Heptagon
open Global
open Initial
open Interference_graph

let rename_states env g = 
  let rename_one n =
    try
      let olds = List.hd n.g_content in
      let s = NamesEnv.find olds env in
	Hashtbl.remove g.g_hash olds;
	Hashtbl.add g.g_hash s n;
	n.g_content <- [s]
    with Not_found -> ()
  in
    List.iter rename_one g.g_nodes

(* the list of enumerated types introduced to represent states *)
let state_type_dec_list = ref []

let intro_type states =
  let list env = NamesEnv.fold (fun _ state l -> state :: l) env [] in
  let n = gen_symbol () in
  let state_type = "st" ^ n in
  state_type_dec_list :=
    (tmake state_type (Type_enum(list states))) :: !state_type_dec_list;
  Name(state_type)

(* an automaton may be a Moore automaton, i.e., with only weak transitions; *)
(* a Mealy one, i.e., with only strong transition or mixed *)
let moore_mealy state_handlers =
  let handler (moore, mealy) { s_until = l1; s_unless = l2 } =
    (moore or (l1 <> []), mealy or (l2 <> [])) in
  List.fold_left handler (false, false) state_handlers

let rec translate_eq g (v, eq_list) eq =
  match eq.eq_desc with
      Eautomaton(state_handlers) ->
        translate_automaton g v eq_list state_handlers
    | Eswitch(e, switch_handlers) ->
        v,
        { eq with eq_desc =
            Eswitch(e, translate_switch_handlers g switch_handlers) }
        :: eq_list
    | Epresent(present_handlers, block) ->
        v, { eq with eq_desc =
            Epresent(translate_present_handlers g present_handlers,
                     translate_block g block) } :: eq_list
    | Ereset(r_eq_list, e) ->
        let v, r_eq_list = translate_eqs g v r_eq_list in
        v, { eq with eq_desc = Ereset(r_eq_list, e) } :: eq_list
    | Eeq _ -> v, eq :: eq_list

and translate_eqs g v eq_list = List.fold_left (translate_eq g) (v, []) eq_list

and translate_block g ({ b_local = v; b_equs = eq_list } as b) =
  let v, eq_list = translate_eqs g v eq_list in
  { b with b_local = v; b_equs = eq_list }

and translate_switch_handlers g handlers =
  let translate_switch_handler { w_name = n; w_block = b } =
    { w_name = n; w_block = translate_block g b } in
  List.map translate_switch_handler handlers

and translate_present_handlers g handlers =
  let translate_present_handler { p_cond = e; p_block = b } =
    { p_cond = e; p_block = translate_block g b } in
  List.map translate_present_handler handlers

and translate_automaton g v eq_list handlers =
  let has_until, has_unless = moore_mealy handlers in
  let states =
    let suffix = gen_symbol () in
    List.fold_left
      (fun env { s_state = n } -> NamesEnv.add n (n ^ suffix) env)
      NamesEnv.empty handlers in

  let statetype = intro_type states in
  let tstatetype = Tbase(Tid(statetype)) in
  let initial = Name(NamesEnv.find (List.hd handlers).s_state states) in

  let statename = Ident.fresh "s" in
  let next_statename = Ident.fresh "ns" in
  let resetname = Ident.fresh "r" in
  let next_resetname = Ident.fresh "nr" in
  let pre_next_resetname = Ident.fresh "pnr" in

  (* update the states graph with the suffixed names *)
  rename_states states g;

  let name n = Name(NamesEnv.find n states) in
  let state n =
    emake (Econst(Cconstr(name n))) tstatetype in
  let statevar n = var n tstatetype in
  let boolvar n = var n tybool in

  let escapes n s rcont =
    let escape { e_cond = e; e_reset = r; e_next_state = n } cont =
      ifthenelse e (pair (state n) (if r then dtrue else dfalse)) cont in
    List.fold_right escape s (pair (state n) rcont) in
  let strong { s_state = n; s_unless = su } =
    block
      (Env.add statename tstatetype
         (Env.add resetname tybool Env.empty))
      ([reset(
          [eq (Etuplepat[Evarpat(statename);Evarpat(resetname)])
             (escapes n su (boolvar pre_next_resetname))])
          (boolvar pre_next_resetname)]) in

  let weak { s_state = n; s_block = b; s_until = su } =
    let b = translate_block g b in
    { b with b_equs =
        [reset ((eq (Etuplepat[Evarpat(next_statename);
                               Evarpat(next_resetname)])
                   (escapes n su dfalse)) :: b.b_equs)
           (boolvar resetname)];
        (* (or_op (boolvar pre_next_resetname) (boolvar resetname))]; *)
        b_defnames =
        Env.add next_statename tstatetype
          (Env.add next_resetname tybool
             b.b_defnames)
    } in
  let v =
      (param next_statename (Tid(statetype))) ::
      (param resetname tbool) ::
      (param next_resetname tbool) ::
      (param pre_next_resetname tbool) :: v in
  (* we optimise the case of an only strong automaton *)
  (* or only weak automaton *)
  match has_until, has_unless with
    | true, false ->
	(* a Moore automaton with only weak transitions *)
	v, (switch (fby_state initial (statevar next_statename))
	       (List.map
		   (fun ({ s_state = n } as case) ->
		     { w_name = name n; w_block = weak case })
		   handlers)) ::
	  (eq (Evarpat pre_next_resetname) 
	      (fby_false (boolvar (next_resetname)))) ::
	      (eq (Evarpat resetname) (boolvar pre_next_resetname)) :: eq_list
    | _ ->
	(* the general case; two switch to generate,
	   statename variable used and defined *)
	(param statename (Tid(statetype))) :: v,
	(switch (fby_state initial (statevar next_statename))
	    (List.map
		(fun ({ s_state = n } as case) ->
		  { w_name = name n; w_block = strong case })
		handlers)) ::
	  (switch (statevar statename)
	      (List.map
		  (fun ({ s_state = n } as case) ->
		    { w_name = name n; w_block = weak case })
		  handlers)) ::
	  (eq (Evarpat pre_next_resetname) 
	      (fby_false (boolvar (next_resetname)))) ::
	  eq_list

let translate_contract g ({ c_local = v; c_eq = eq_list} as c) =
  let v, eq_list = translate_eqs g v eq_list in
  { c with c_local = v; c_eq = eq_list }

let node ({ n_local = v; n_equs = eq_list; n_contract = contract; n_states_graph = g } as n) =
  let v, eq_list = translate_eqs g v eq_list in
  let contract = optional (translate_contract g) contract in
  { n with n_local = v; n_equs = eq_list; n_contract = contract }

let program ({ p_types = pt_list; p_nodes = n_list } as p) =
  let n_list = List.map node n_list in
  { p with p_types = !state_type_dec_list @ pt_list;
      p_nodes = n_list }

(*
  A -> do ... unless c1 then A1 ... until c'1 then A'1 ...

  match A fby next_state with
  A -> resA = pre_next_res or (if c1 then ... else ..

  match state with
  A -> reset
  next_res = if c'1 then true else ... else false
  every resA

  if faut donc: - une memoire pour pre(next_res) + n memoires (pre(resA),...)

  merge state
  (A -> reset ... when A(state) every pre_next_res or res)
*)
