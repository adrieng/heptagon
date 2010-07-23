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

open Misc
open Names
open Idents
open Heptagon
open Types

let mk_var_exp n ty =
  mk_exp (Evar n) ty

let mk_pair e1 e2 =
  mk_exp (mk_op_app Etuple [e1;e2]) (Tprod [e1.e_ty; e2.e_ty])

let mk_reset_equation eq_list e =
  mk_equation (Ereset (eq_list, e))

let mk_switch_equation e l =
  mk_equation (Eswitch (e, l))

let mk_exp_fby_false e =
  mk_exp (Epre (Some (mk_static_exp (Sconstructor Initial.pfalse)), e))
    (Tid Initial.pbool)

let mk_exp_fby_state initial e =
  { e with e_desc = Epre (Some (mk_static_exp (Sconstructor initial)), e) }

(* the list of enumerated types introduced to represent states *)
let state_type_dec_list = ref []

let intro_type states =
  let list env = NamesEnv.fold (fun _ state l -> state :: l) env [] in
  let n = gen_symbol () in
  let state_type = "st" ^ n in
  state_type_dec_list :=
    (mk_type_dec state_type (Type_enum (list states))) :: !state_type_dec_list;
  Name(state_type)

(* an automaton may be a Moore automaton, i.e., with only weak transitions; *)
(* a Mealy one, i.e., with only strong transition or mixed *)
let moore_mealy state_handlers =
  let handler (moore, mealy) { s_until = l1; s_unless = l2 } =
    (moore or (l1 <> []), mealy or (l2 <> [])) in
  List.fold_left handler (false, false) state_handlers

let rec translate_eq (v, eq_list) eq =
  match eq.eq_desc with
      Eautomaton(state_handlers) ->
        translate_automaton v eq_list state_handlers
    | Eswitch(e, switch_handlers) ->
        let eq = { eq with eq_desc =
            Eswitch(e, translate_switch_handlers switch_handlers) } in
        v, eq::eq_list
    | Epresent(present_handlers, block) ->
        let eq = { eq with eq_desc =
            Epresent(translate_present_handlers present_handlers,
                     translate_block block) } in
        v, eq::eq_list
    | Ereset(r_eq_list, e) ->
        let v, r_eq_list = translate_eqs v r_eq_list in
        let eq = { eq with eq_desc = Ereset(r_eq_list, e) } in
        v,  eq::eq_list
    | Eeq _ -> v, eq :: eq_list

and translate_eqs v eq_list = List.fold_left translate_eq (v, []) eq_list

and translate_block ({ b_local = v; b_equs = eq_list } as b) =
  let v, eq_list = translate_eqs v eq_list in
  { b with b_local = v; b_equs = eq_list }

and translate_switch_handlers handlers =
  let translate_switch_handler { w_name = n; w_block = b } =
    { w_name = n; w_block = translate_block b } in
  List.map translate_switch_handler handlers

and translate_present_handlers handlers =
  let translate_present_handler { p_cond = e; p_block = b } =
    { p_cond = e; p_block = translate_block b } in
  List.map translate_present_handler handlers

and translate_automaton v eq_list handlers =
  let has_until, has_unless = moore_mealy handlers in
  let states =
    let suffix = gen_symbol () in
    List.fold_left
      (fun env { s_state = n } -> NamesEnv.add n (n ^ suffix) env)
      NamesEnv.empty handlers in

  let statetype = intro_type states in
  let tstatetype = Tid statetype in
  let initial = Name(NamesEnv.find (List.hd handlers).s_state states) in

  let statename = Idents.fresh "s" in
  let next_statename = Idents.fresh "ns" in
  let resetname = Idents.fresh "r" in
  let next_resetname = Idents.fresh "nr" in
  let pre_next_resetname = Idents.fresh "pnr" in

  let name n = Name(NamesEnv.find n states) in
  let state n = mk_exp (Econst (mk_static_exp
                                  (Sconstructor (name n)))) tstatetype in
  let statevar n = mk_var_exp n tstatetype in
  let boolvar n = mk_var_exp n (Tid Initial.pbool) in

  let escapes n s rcont =
    let escape { e_cond = e; e_reset = r; e_next_state = n } cont =
      mk_ifthenelse e (mk_pair (state n) (if r then dtrue else dfalse)) cont
    in
    List.fold_right escape s (mk_pair (state n) rcont)
  in

  let strong { s_state = n; s_unless = su } =
    let defnames = Env.add resetname (Tid Initial.pbool) Env.empty in
    let defnames = Env.add statename tstatetype defnames in
    let st_eq = mk_simple_equation
      (Etuplepat[Evarpat(statename); Evarpat(resetname)])
      (escapes n su (boolvar pre_next_resetname)) in
    mk_block defnames [mk_reset_equation [st_eq]
                         (boolvar pre_next_resetname)]
  in

  let weak { s_state = n; s_block = b; s_until = su } =
    let b = translate_block b in
    let defnames = Env.add next_resetname (Tid Initial.pbool) b.b_defnames in
    let defnames = Env.add next_statename tstatetype defnames in
    let ns_eq = mk_simple_equation
      (Etuplepat[Evarpat(next_statename); Evarpat(next_resetname)])
      (escapes n su dfalse) in
    { b with b_equs =
        [mk_reset_equation (ns_eq::b.b_equs) (boolvar resetname)];
        (* (or_op (boolvar pre_next_resetname) (boolvar resetname))]; *)
        b_defnames = defnames;
    }
  in

  let v =
    (mk_var_dec next_statename (Tid(statetype))) ::
      (mk_var_dec resetname (Tid Initial.pbool)) ::
      (mk_var_dec next_resetname (Tid Initial.pbool)) ::
      (mk_var_dec pre_next_resetname (Tid Initial.pbool)) :: v in
  (* we optimise the case of an only strong automaton *)
  (* or only weak automaton *)
  match has_until, has_unless with
    | true, false ->
        let switch_e = mk_exp_fby_state initial (statevar next_statename) in
        let switch_handlers = (List.map
                                 (fun ({ s_state = n } as case) ->
                                    { w_name = name n; w_block = weak case })
                                 handlers) in
        let switch_eq = mk_switch_equation switch_e switch_handlers in
        let nr_eq = mk_simple_equation (Evarpat pre_next_resetname)
          (mk_exp_fby_false (boolvar (next_resetname))) in
        let pnr_eq = mk_simple_equation (Evarpat resetname)
          (boolvar pre_next_resetname) in
        (* a Moore automaton with only weak transitions *)
        v, switch_eq :: nr_eq :: pnr_eq :: eq_list
    | _ ->
        (* the general case; two switch to generate,
           statename variable used and defined *)
        let v = (mk_var_dec statename (Tid statetype)) :: v in

        let ns_switch_e = mk_exp_fby_state initial (statevar next_statename) in
        let ns_switch_handlers = List.map
          (fun ({ s_state = n } as case) ->
             { w_name = name n; w_block = strong case })
          handlers in
        let ns_switch_eq = mk_switch_equation ns_switch_e ns_switch_handlers in

        let switch_e = statevar statename in
        let switch_handlers = List.map
          (fun ({ s_state = n } as case) ->
             { w_name = name n; w_block = weak case })
          handlers in
        let switch_eq = mk_switch_equation switch_e switch_handlers in

        let pnr_eq = mk_simple_equation (Evarpat pre_next_resetname)
          (mk_exp_fby_false (boolvar (next_resetname))) in
        v, ns_switch_eq :: switch_eq :: pnr_eq :: eq_list

let translate_contract ({ c_local = v; c_eq = eq_list} as c) =
  let v, eq_list = translate_eqs v eq_list in
  { c with c_local = v; c_eq = eq_list }

let node ({ n_local = v; n_equs = eq_list; n_contract = contract } as n) =
  let v, eq_list = translate_eqs v eq_list in
  let contract = optional translate_contract contract in
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
