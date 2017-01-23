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
(* clock checking *)

(* v_clock is expected to contain correct clocks before entering here :
     either explicit with Cbase representing the node activation clock
     or fresh_clock() for unannoted variables.
  Idem for e_ct : if explicit, it represents a clock annotation.
  Unification is done on this mutable fields.
  e_base_ck is set according to node signatures.

 *)

open Idents
open Names
open Minils
open Global_printer
open Mls_printer
open Signature
open Clocks
open Location
open Format

(** Error Kind *)
type error_kind =
  | Etypeclash of ct * ct
  | Eclockclash of Clocks.ck * Clocks.ck
  | Edefclock

let error_message loc = function
  | Etypeclash (actual_ct, expected_ct) ->
      Format.eprintf "%aClock Clash: this expression has clock %a,@\n\
                        but is expected to have clock %a.@."
        print_location loc
        print_ct actual_ct
        print_ct expected_ct;
      raise Errors.Error
  | Eclockclash (actual_ck, expected_ck) ->
      Format.eprintf "%aClock Clash: this value has clock %a,@\n\
                        but is expected to have clock %a.@."
        print_location loc
        print_ck actual_ck
        print_ck expected_ck;
      raise Errors.Error
  | Edefclock ->
      Format.eprintf "%aArguments defining clocks should be given as names@."
        print_location loc;
      raise Errors.Error


let ck_of_name h x =
  if is_reset x
  then fresh_clock()
  else
    try Env.find x h
    with Not_found ->
      (* Format.eprintf "looking for %a/%d@." print_ident x x.num; *)
      (* Env.iter (fun k ck -> Format.eprintf "%a/%d => %a@." print_ident k k.num print_ck ck) h; *)
      Misc.internal_error ("clocking: unknown clock name " ^ name x)

let rec typing_extvalue h w =
  let ck = match w.w_desc with
    | Wconst _ -> fresh_clock()
    | Wvar x -> ck_of_name h x
    | Wwhen (w1, c, n) ->
        let ck_n = ck_of_name h n in
        expect_extvalue h ck_n w1;
        Clocks.Con (ck_n, c, n)
    | Wfield (w1, _) ->
        typing_extvalue h w1
    | Wreinit (w1, w2) ->
      let t1 = typing_extvalue h w1 in
      let t2 = typing_extvalue h w2 in
      unify_ck t1 t2;
      t1
  in
  (try unify_ck ck w.w_ck
   with Unify ->
     eprintf "Incoherent clock annotation for extvalue %a.@\n"
       Mls_printer.print_extvalue w;
     error_message w.w_loc (Etypeclash (Ck ck, Ck w.w_ck)));
  w.w_ck <- ck;
  ck

and expect_extvalue h expected_ck e =
  let actual_ck = typing_extvalue h e in
  try unify_ck actual_ck expected_ck
  with
  | Unify -> eprintf "%a : " print_extvalue e;
      error_message e.w_loc (Eclockclash (actual_ck, expected_ck))

let rec typing_pat h = function
  | Evarpat x -> Ck (ck_of_name h x)
  | Etuplepat pat_list -> Cprod (List.map (typing_pat h) pat_list)


let typing_app h base pat op w_list = match op with
  | Earray_fill | Eselect | Eselect_dyn | Eselect_trunc | Eupdate | Eequal
  | Eselect_slice | Econcat | Earray | Efield_update | Eifthenelse ->
      List.iter (expect_extvalue h base) w_list;
      Ck base
  | Efun { qual = Module "Iostream"; name = "printf" }
  | Efun { qual = Module "Iostream"; name = "fprintf" } ->
    List.iter (expect_extvalue h base) w_list;
    Cprod []
  | ( Efun f | Enode f) ->
      let node = Modules.find_value f in
      let pat_id_list = Mls_utils.ident_list_of_pat pat in
      let rec build_env a_l v_l env = match a_l, v_l with
        | [],[] -> env
        | a::a_l, v::v_l -> (match a.a_name with
          | None -> build_env a_l v_l env
          | Some n -> build_env a_l v_l ((n,v)::env))
        | _ -> Misc.internal_error ("Clocking, non matching signature in call of " ^
                                      Names.fullname f)
      in
      let env_pat = build_env node.node_outputs pat_id_list [] in
      let env_args = build_env node.node_inputs w_list [] in
      (* implement with Cbase as base, replace name dep by ident dep *)
      let rec sigck_to_ck sck = match sck with
        | Signature.Cbase -> base
        | Signature.Con (sck,c,x) ->
            (* find x in the envs : *)
            let id = try List.assoc x env_pat
                     with Not_found ->
                       try
                         let w = List.assoc x env_args in
                         (match w.w_desc with
                           | Wvar id -> id
                           | _ -> error_message w.w_loc Edefclock)
                       with Not_found ->
                         Misc.internal_error "Clocking, non matching signature 2"
            in
            Clocks.Con (sigck_to_ck sck, c, id)
      in
      List.iter2 (fun a w -> expect_extvalue h (sigck_to_ck a.a_clock) w) node.node_inputs w_list;
      Clocks.prod (List.map (fun a -> sigck_to_ck a.a_clock) node.node_outputs)


let rec stateful e = match e.e_desc with
  | Efby _ -> true
  | Ewhen (e,_,_) -> stateful e
  | Eapp({a_unsafe = unsafe}, _, _) when unsafe -> true
  | Eapp({a_op = Enode _}, _, _) -> true
  | _ -> false


let typing_eq h ({ eq_lhs = pat; eq_rhs = e; eq_loc = loc } as eq) =
  (* typing the expression, returns ct, ck_base *)
  let rec typing e =
    let ct,base = match e.e_desc with
      | Eextvalue w
      | Efby (_, w) ->
          let ck = typing_extvalue h w in
          Ck ck, ck
      | Ewhen (e,c,n) ->
          let ck_n = ck_of_name h n in
          let _base = expect (skeleton ck_n e.e_ty) e in
          let base_ck = if stateful e then ck_n else Clocks.Con (ck_n, c, n) in
          skeleton (Clocks.Con (ck_n, c, n)) e.e_ty, base_ck
      | Emerge (x, c_e_list) ->
          let ck = ck_of_name h x in
          List.iter (fun (c,e) -> expect_extvalue h (Clocks.Con (ck,c,x)) e) c_e_list;
          Ck ck, ck
      | Estruct l ->
          let ck = fresh_clock () in
          List.iter (fun (_, e) -> expect_extvalue h ck e) l;
          Ck ck, ck
      | Eapp({a_op = op}, args, _) -> (* hyperchronous reset *)
          let base_ck = fresh_clock () in
          let ct = typing_app h base_ck pat op args in
          ct, base_ck
      | Eiterator (it, {a_op = op}, nl, pargs, args, _) -> (* hyperchronous reset *)
          let base_ck = fresh_clock() in
          let ct = match it with
            | Imap -> (* exactly as if clocking the node *)
                typing_app h base_ck pat op (pargs@args)
            | Imapi -> (* clocking the node with the extra i input on [ck_r] *)
                let il (* stubs i as 0 *) =
                  List.map (fun _ -> mk_extvalue ~ty:Initial.tint ~linearity:Linearity.Ltop
                    ~clock:base_ck (Wconst (Initial.mk_static_int 0))) nl
                in
                typing_app h base_ck pat op (pargs@args@il)
            | Ifold | Imapfold ->
                (* clocking node with equality constaint on last input and last output *)
                let ct = typing_app h base_ck pat op (pargs@args) in
                unify_ck (Clocks.last_clock ct) (Misc.last_element args).w_ck;
                ct
            | Ifoldi -> (* clocking the node with the extra i and last in/out constraints *)
                let il (* stubs i as 0 *) =
                  List.map (fun _ -> mk_extvalue ~ty:Initial.tint ~linearity:Linearity.Ltop
                    ~clock:base_ck (Wconst (Initial.mk_static_int 0))) nl
                in
                let rec insert_i args = match args with
                  | [] -> il
                  | [l] -> il @ [l]
                  | h::l -> h::(insert_i l)
                in
                let ct = typing_app h base_ck pat op (pargs@(insert_i args)) in
                unify_ck (Clocks.last_clock ct) (Misc.last_element args).w_ck;
                ct
          in
          ct, base_ck
    in
    (try unify ct e.e_ct
     with Unify ->
       eprintf "Inconsistent clock annotation for exp %a.@\n"
       Mls_printer.print_exp e;
       error_message e.e_loc (Etypeclash (ct,e.e_ct)));
    e.e_ct <- ct;
    ct, base
  and expect expected_ct e =
    let actual_ct,base = typing e in
    (try unify actual_ct expected_ct
     with Unify -> error_message e.e_loc (Etypeclash (actual_ct, expected_ct)));
    base
  in
  let ct,base_ck = typing e in
  let pat_ct = typing_pat h pat in
  (try unify ct pat_ct
    with Unify ->
      eprintf "Incoherent clock between right and left side of the equation.@\n";
      error_message loc (Etypeclash (ct, pat_ct)));
  { eq with eq_base_ck = base_ck }

let typing_eqs h eq_list = List.rev_map (typing_eq h) eq_list

let append_env h vds =
  List.fold_left (fun h { v_ident = n; v_clock = ck } -> Env.add n ck h) h vds


let typing_contract h0 h contract =
  match contract with
    | None -> None, h
    | Some ({ c_local = l_list;
             c_eq = eq_list;
             c_assume = e_a;
             c_objectives = objs;
             c_assume_loc = e_a_loc;
             c_enforce_loc = e_g_loc;
             c_controllables = c_list } as contract) ->
        let h' = append_env h0 l_list in
        (* assumption *)
        (* property *)
        let eq_list = typing_eqs h' eq_list in
        expect_extvalue h' Clocks.Cbase e_a;
        List.iter (fun o -> expect_extvalue h' Clocks.Cbase o.o_exp) objs;
        expect_extvalue h Clocks.Cbase e_a_loc;
        expect_extvalue h Clocks.Cbase e_g_loc;
        let h = append_env h c_list in
        Some { contract with c_eq = eq_list }, h

let rec constrain_on loc h = function
  | Clocks.Cbase | Clocks.Cvar _ -> ()
  | Clocks.Con (ck', c, n) ->
      (try unify_ck (ck_of_name h n) ck'
       with Unify -> error_message loc (Eclockclash (ck_of_name h n, ck')));
      constrain_on loc h ck'

let constrain_on_over h xs =
  List.iter (fun vd -> constrain_on vd.v_loc h (ck_of_name h vd.v_ident)) xs

let typing_node node =
  let h0 = append_env Env.empty node.n_input in
  let h0 = append_env h0 node.n_output in
  let h = append_env h0 node.n_local in
  constrain_on_over h node.n_input;
  constrain_on_over h node.n_output;
  constrain_on_over h node.n_local;
  let contract, h = typing_contract h0 h node.n_contract in
  (*   let h = append_env h node.n_local in *)
  let equs = typing_eqs h node.n_equs in
  (* synchronize input and output on base : find the free vars and set them to base *)
  Env.iter (fun _ ck -> unify_ck Clocks.Cbase (root_ck_of ck)) h0;
  (*update clock info in variables descriptions *)
  let set_clock vd = { vd with v_clock = ck_repr (Env.find vd.v_ident h) } in
  let node = { node with n_input = List.map set_clock node.n_input;
                         n_output = List.map set_clock node.n_output;
                         n_local = List.rev_map set_clock node.n_local;
                         n_equs = equs;
                         n_contract = contract; }
  in
  let sign = Mls_utils.signature_of_node node in
  Check_signature.check_signature sign;
  Modules.replace_value node.n_name sign;
  node

let program p =
  let program_desc pd = match pd with
    | Pnode nd -> Pnode (typing_node nd)
    | _ -> pd
  in
    { p with p_desc = List.map program_desc p.p_desc; }
