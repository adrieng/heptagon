(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* causality check *)

open Misc
open Names
open Idents
open Heptagon
open Location
open Graph
open Causal

let cempty = Cempty
let is_empty c = (c = cempty)

let cand c1 c2 =
  match c1, c2 with
    | Cempty, _ -> c2 | _, Cempty -> c1
    | c1, c2 -> Cand(c1, c2)
let rec candlist l =
  match l with
    | [] -> Cempty
    | c1 :: l -> cand c1 (candlist l)

let ctuplelist l =
  Ctuple l

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
let lastread x = Clastread(x)
let cwrite x = Cwrite(x)

(* cutting dependences with a delay operator *)
let rec pre = function
  | Cor(c1, c2) -> Cor(pre c1, pre c2)
  | Cand(c1, c2) -> Cand(pre c1, pre c2)
  | Ctuple l -> Ctuple (List.map pre l)
  | Cseq(c1, c2) -> Cseq(pre c1, pre c2)
  | Cread _ -> Cempty
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
      | Cwrite(id) | Cread(id) | Clastread(id) ->
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
    | Evar(x) -> read x
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
    | Eiterator (_, _, _, e_list, _) ->
        ctuplelist (List.map typing e_list)
    | Ewhen (e, c, ce) ->
        let t = typing e in
        let tc = typing ce in
        cseq tc t
    | Emerge (e, c_e_list) ->
        let t = typing e in
        let tl = List.map (fun (_,e) -> typing e) c_e_list in
        cseq t (candlist tl)


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
        cseq t1 (cor i2 i3)
    | (Eequal | Efun _| Enode _ | Econcat | Eselect_slice
      | Eselect_dyn| Eselect _ | Earray_fill) ->
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
    | Ebang -> let e = assert_1 e_list in typing e

let rec typing_pat = function
  | Evarpat(x) -> cwrite(x)
  | Etuplepat(pat_list) ->
      candlist (List.map typing_pat pat_list)

(** Typing equations *)
let rec typing_eqs eq_list = candlist (List.map typing_eq eq_list)

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
  corlist (List.map handler handlers)

and typing_present handlers b =
  let handler { p_cond = e; p_block = b } =
    cseq (typing e) (typing_block b) in
  corlist ((typing_block b) :: (List.map handler handlers))

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
  corlist (List.map handler state_handlers)

and typing_block { b_local = dec; b_equs = eq_list; b_loc = loc } =
  let teq = typing_eqs eq_list in
  Causal.check loc teq;
  clear (build dec) teq

let typing_contract loc contract =
  match contract with
    | None -> cempty
    | Some { c_block = b; c_assume = e_a;
             c_enforce = e_g } ->
        let teq = typing_eqs b.b_equs in
        let t_contract = cseq (typing e_a) (cseq teq (typing e_g)) in
        Causal.check loc t_contract;
        let t_contract = clear (build b.b_local) t_contract in
        t_contract

let typing_node { n_contract = contract;
                  n_block = b; n_loc = loc } =
  let _ = typing_contract loc contract in
    ignore (typing_block b)

let program ({ p_nodes = p_node_list } as p) =
  List.iter typing_node p_node_list;
  p

