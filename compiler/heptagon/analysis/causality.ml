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

(* causality check *)

open Misc
open Idents
open Heptagon
open Linearity
open Causal

let cempty = Cempty
let is_empty c = (c = cempty)

let cand c1 c2 =
  match c1, c2 with
    | Cempty, _ -> c2 | _, Cempty -> c1
    | c1, c2 -> Cand(c1, c2)
let candlist l =
  let rec candlist_aux acc l =
    match l with
    | [] -> acc
    | [c] -> cand acc c
    | c1 :: l -> candlist_aux (cand c1 acc) l in
  match l with
  | [] -> Cempty
  | c :: l -> candlist_aux c l

let ctuplelist l = match l with
  | [c] -> c
  | _ -> Ctuple l

let cor c1 c2 =
  match c1, c2 with
    | Cempty, Cempty -> Cempty
    | _ -> Cor(c1, c2)
let rec corlist l =
  match l with
    | [] -> Cempty
    | [c1] -> c1
    | c1 :: l -> cor c1 (corlist l)

let cseq c1 c2 =
  match c1, c2 with
    | Cempty, _ -> c2
    | _, Cempty -> c1
    | c1, c2 -> Cseq(c1, c2)
let rec cseqlist l =
  match l with
    | [] -> Cempty
    | c1 :: l -> cseq c1 (cseqlist l)

let read x = Cread(x)
let linread x = Clinread(x)
let lastread x = Clastread(x)
let cwrite x = Cwrite(x)

(* cutting dependences with a delay operator *)
let rec pre = function
  | Cor(c1, c2) -> Cor(pre c1, pre c2)
  | Cand(c1, c2) -> Cand(pre c1, pre c2)
  | Ctuple l -> Ctuple (List.map pre l)
  | Cseq(c1, c2) -> Cseq(pre c1, pre c2)
  | Cread _ | Clinread _ -> Cempty
  | (Cwrite _ | Clastread _ | Cempty) as c -> c

(* projection and restriction *)
let clear env c =
  let rec clearec c =
    match c with
      | Cor(c1, c2) ->
          let c1 = clearec c1 in
          let c2 = clearec c2 in
          cor c1 c2
      | Cand(c1, c2) ->
          let c1 = clearec c1 in
          let c2 = clearec c2 in
          cand c1 c2
      | Cseq(c1, c2) ->
          let c1 = clearec c1 in
          let c2 = clearec c2 in
          cseq c1 c2
      | Ctuple l -> Ctuple (List.map clearec l)
      | Cwrite(id) | Cread(id) | Clinread(id) | Clastread(id) ->
          if IdentSet.mem id env then Cempty else c
      | Cempty -> c in
  clearec c

let build dec =
  let add acc { v_ident = n; } = IdentSet.add n acc in
  List.fold_left add IdentSet.empty dec

(** Main typing function *)
let rec typing e =
  match e.e_desc with
    | Econst _ -> cempty
    | Evar(x) ->
        (match e.e_linearity with
          | Lat _ -> linread x
          | _ -> read x)
    | Elast(x) -> lastread x
    | Epre (_, e) -> pre (typing e)
    | Efby (e1, e2) ->
        let t1 = typing e1 in
        let t2 = pre (typing e2) in
          candlist [t1; t2]
    | Eapp({ a_op = op }, e_list, _) -> apply op e_list
    | Estruct(l) ->
        let l = List.map (fun (_, e) -> typing e) l in
        candlist l
    | Eiterator (_, _, _, pe_list, e_list, _) ->
        ctuplelist (List.map typing (pe_list@e_list))
    | Ewhen (e, _, x) ->
        let t = typing e in
        let tc = read x in
        cseq tc t
    | Emerge (x, c_e_list) ->
        let t = read x in
        let tl = List.map (fun (_,e) -> typing e) c_e_list in
        cseq t (candlist tl)
    | Esplit(c, e) ->
        let t = typing c in
        let te = typing e in
          cseq t te


(** Typing an application *)
and apply op e_list =
  match op with
    | Earrow ->
        let e1, e2 = assert_2 e_list in
        let t1 = typing e1 in
        let t2 = typing e2 in
        candlist [t1; t2]
    | Efield ->
      let e1 = assert_1 e_list in
        typing e1
    | Eifthenelse ->
        let e1, e2, e3 = assert_3 e_list in
        let t1 = typing e1 in
        let i2 = typing e2 in
        let i3 = typing e3 in
        ctuplelist [t1; i2; i3]
    | ( Efun _| Enode _ | Econcat | Eselect_slice
      | Eselect_dyn | Eselect_trunc | Eselect | Earray_fill | Ereinit) ->
        ctuplelist (List.map typing e_list)
    | (Earray | Etuple) ->
        candlist (List.map typing e_list)
    | Efield_update ->
        let e1, e2 = assert_2 e_list in
        let t1 = typing e1 in
        let t2 = typing e2 in
        cseq t2 t1
    | Eupdate ->
        let e1, e_list = assert_1min e_list in
        let t1 = typing e1 in
        let t2 = ctuplelist (List.map typing e_list) in
          cseq t2 t1

let rec typing_pat = function
  | Evarpat(x) -> cwrite(x)
  | Etuplepat(pat_list) ->
      candlist (List.map typing_pat pat_list)

(** Typing equations *)
let rec typing_eqs eq_list = candlist (List.rev_map typing_eq eq_list)

and typing_eq eq =
  match eq.eq_desc with
    | Eautomaton(handlers) -> typing_automaton handlers
    | Eswitch(e, handlers) ->
        cseq (typing e) (typing_switch handlers)
    | Epresent(handlers, b) ->
        typing_present handlers b
    | Ereset(b, e) ->
        cseq (typing e) (typing_block b)
    | Eblock b ->
        typing_block b
    | Eeq(pat, e) ->
        cseq (typing e) (typing_pat pat)

and typing_switch handlers =
  let handler { w_block = b } = typing_block b in
  candlist (List.map handler handlers)

and typing_present handlers b =
  let handler { p_cond = e; p_block = b } =
    cseq (typing e) (typing_block b) in
  candlist ((typing_block b) :: (List.map handler handlers))

and typing_automaton state_handlers =
  (* typing the body of the automaton *)
  let handler
      { s_state = _; s_block = b; s_until = suntil; s_unless = sunless } =
    let escape { e_cond = e } = typing e in

    (* typing the body *)
    let tb = typing_block b in
    let t1 = candlist (List.map escape suntil) in
    let t2 = candlist (List.map escape sunless) in

    cseq t2 (cseq tb t1) in
  candlist (List.map handler state_handlers)

and typing_block { b_local = _dec; b_equs = eq_list; b_loc = _loc } =
  (*let teq = typing_eqs eq_list in
    Causal.check loc teq;
    clear (build dec) teq *)
  typing_eqs eq_list

let typing_contract loc contract =
  match contract with
    | None -> cempty
    | Some { c_block = b;
             c_assume = e_a;
             c_assume_loc = e_a_loc;
             c_objectives = objs;
             c_enforce_loc = e_g_loc;
           } ->
        let teq = typing_eqs b.b_equs in
        let t_contract =
          cseq
            teq
            (ctuplelist
               ((typing e_a) ::
                (typing e_a_loc) ::
                (typing e_g_loc) ::
                  (List.map (fun o -> typing o.o_exp) objs)
            )) in
        Causal.check loc t_contract;
        let t_contract = clear (build b.b_local) t_contract in
        t_contract

let typing_node { n_contract = contract;
                  n_block = b; n_loc = loc } =
  let _ = typing_contract loc contract in
  let teq = typing_block b in
    Causal.check loc teq

let program ({ p_desc = pd } as p) =
  List.iter (function Pnode n -> typing_node n | _ -> ()) pd;
  p
