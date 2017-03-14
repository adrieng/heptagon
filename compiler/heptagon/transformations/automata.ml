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
(* removing automata statements *)

(* TODO deal correctly with [stateful] and [unsafe] *)

open Types
open Names
open Idents
open Heptagon
open Hept_utils
open Hept_mapfold
open Initial

type var = S | NS | R | NR | PNR
let fresh = Idents.gen_fresh "automata"
  (function S -> "s" | NS -> "ns" | R -> "r" | NR -> "nr" | PNR -> "pnr")

let mk_var_exp n ty =
  mk_exp (Evar n) ty ~linearity:Linearity.Ltop

let mk_pair e1 e2 =
  mk_exp (mk_op_app Etuple [e1;e2]) (Tprod [e1.e_ty; e2.e_ty])
    ~linearity:(Linearity.Ltuple [Linearity.Ltop; Linearity.Ltop])

let mk_reset_equation eq_list e =
  mk_equation (Ereset (mk_block eq_list, e))

let mk_switch_equation e l =
  mk_equation (Eswitch (e, l))

let mk_exp_fby_false e =
  mk_exp (Epre (Some (mk_static_bool false), e))
    (Tid Initial.pbool) ~linearity:Linearity.Ltop

let mk_constructor constr ty =
  mk_static_exp ty (Sconstructor constr)

(* Be sure that [initial] is of the right type [e.e_ty] before using this *)
let mk_exp_fby_state initial e =
  { e with e_desc = Epre (Some (mk_constructor initial e.e_ty), e) }

(* the list of enumerated types introduced to represent states *)
let state_type_dec_list = ref []


(* create and add to the env the constructors corresponding to a name state *)
let intro_state_constr type_name state state_env =
  let n = String.capitalize_ascii (Names.shortname type_name) ^ "_" ^ state in
  let c = Modules.fresh_constr "automata" n in
  Modules.add_constrs c type_name; NamesEnv.add state c state_env

(* create and add the the global env and to state_type_dec_list
   a type corresponding to the state env*)
let intro_type type_name state_env =
  let state_constrs = NamesEnv.fold (fun _ c c_l -> c::c_l) state_env [] in
  (* Add the new type to the env *)
  Modules.add_type type_name (Signature.Tenum state_constrs);
  (* Add the new type to the types to add to the Ast *)
  state_type_dec_list :=
    Ptype (mk_type_dec type_name (Type_enum state_constrs)) :: !state_type_dec_list

(** Allows to classify an automaton :
    Moore automatons doesn't have strong transitions,
    Mealy automatons may have some. *)
let no_strong_transition state_handlers =
  let handler no_strong { s_unless = l } = no_strong && (l = []) in
  List.fold_left handler true state_handlers


let translate_automaton v eq_list handlers =
  let type_name = Modules.fresh_type "automata" "st" in
  (* the state env associate a name to a qualified constructor *)
  let state_env =
    List.fold_left
      (fun env { s_state = n } -> intro_state_constr type_name n env)
      NamesEnv.empty handlers in
  intro_type type_name state_env;
  let tstatetype = Tid type_name in

  (* The initial state constructor *)
  let initial = (NamesEnv.find (List.hd handlers).s_state state_env) in

  let statename = fresh S in
  let next_statename = fresh NS in
  let resetname = fresh R in
  let next_resetname = fresh NR in
  let pre_next_resetname = fresh PNR in

  let name n = NamesEnv.find n state_env in
  let state n =
    mk_exp (Econst (mk_constructor (name n) tstatetype)) tstatetype ~linearity:Linearity.Ltop
  in
  let statevar n = mk_var_exp n tstatetype in
  let boolvar n = mk_var_exp n (Tid Initial.pbool) in

  let escapes n s rcont =
    let escape { e_cond = e; e_reset = r; e_next_state = n } cont =
      mk_ifthenelse e (mk_pair (state n) (if r then dtrue else dfalse)) cont
    in
    List.fold_right escape s (mk_pair (state n) rcont)
  in

  let strong { s_state = n; s_unless = su } =
    let rst_vd = mk_var_dec resetname (Tid Initial.pbool) ~linearity:Linearity.Ltop in
    let defnames = Env.add resetname rst_vd Env.empty in
    let state_vd = mk_var_dec statename tstatetype ~linearity:Linearity.Ltop in
    let defnames = Env.add statename state_vd defnames in
    let st_eq = mk_simple_equation
      (Etuplepat[Evarpat(statename); Evarpat(resetname)])
      (escapes n su (boolvar pre_next_resetname)) in
    mk_block ~defnames:defnames [mk_reset_equation [st_eq]
                                   (boolvar pre_next_resetname)]
  in

  let weak { s_state = n; s_block = b; s_until = su } =
    let nextrst_vd = mk_var_dec next_resetname (Tid Initial.pbool) ~linearity:Linearity.Ltop in
    let defnames = Env.add next_resetname nextrst_vd b.b_defnames in
    let nextstate_vd = mk_var_dec next_statename tstatetype ~linearity:Linearity.Ltop in
    let defnames = Env.add next_statename nextstate_vd defnames in
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
    (mk_var_dec next_statename tstatetype ~linearity:Linearity.Ltop) ::
      (mk_var_dec resetname (Tid Initial.pbool) ~linearity:Linearity.Ltop) ::
      (mk_var_dec next_resetname (Tid Initial.pbool) ~linearity:Linearity.Ltop) ::
      (mk_var_dec pre_next_resetname (Tid Initial.pbool) ~linearity:Linearity.Ltop) :: v in
  if no_strong_transition handlers
  then (* Only weak transitions : a Moore automaton. *)
    let switch_e = mk_exp_fby_state initial (statevar next_statename) in
    let switch_handlers =
      List.map (fun ({ s_state = n } as case) ->
                  { w_name = name n; w_block = weak case })
               handlers in
    let switch_eq = mk_switch_equation switch_e switch_handlers in
    let nr_eq =
      mk_simple_equation (Evarpat pre_next_resetname)
                         (mk_exp_fby_false (boolvar (next_resetname))) in
    let pnr_eq =
      mk_simple_equation (Evarpat resetname) (boolvar pre_next_resetname) in
    v, switch_eq :: nr_eq :: pnr_eq :: eq_list
  else (* General case,
          two switch to generate statename variable used and defined *)
    let v = (mk_var_dec statename tstatetype ~linearity:Linearity.Ltop) :: v in
    let ns_switch_e = mk_exp_fby_state initial (statevar next_statename) in
    let ns_switch_handlers =
      List.map (fun ({ s_state = n } as case) ->
                  { w_name = name n; w_block = strong case })
               handlers in
    let ns_switch_eq = mk_switch_equation ns_switch_e ns_switch_handlers in
    let switch_e = statevar statename in
    let switch_handlers =
      List.map (fun ({ s_state = n } as case) ->
                  { w_name = name n; w_block = weak case })
               handlers in
    let switch_eq = mk_switch_equation switch_e switch_handlers in
    let pnr_eq =
      mk_simple_equation (Evarpat pre_next_resetname)
                         (mk_exp_fby_false (boolvar (next_resetname))) in
    v, ns_switch_eq :: switch_eq :: pnr_eq :: eq_list

let eq funs (v, eq_list) eq =
  let eq, (v, eq_list) = Hept_mapfold.eq funs (v, eq_list) eq in
    match eq.eq_desc with
      | Eautomaton state_handlers ->
          eq, translate_automaton v eq_list state_handlers
      | _ -> eq, (v, eq::eq_list)

let block funs acc b =
  let b, (v, acc_eq_list) = Hept_mapfold.block funs ([], []) b in
    { b with b_local = v @ b.b_local; b_equs = acc_eq_list }, acc

let program p =
  let funs = { Hept_mapfold.defaults
               with eq = eq; block = block } in
  let p, _ = Hept_mapfold.program_it funs ([],[]) p in
    { p with p_desc = !state_type_dec_list @ p.p_desc }
