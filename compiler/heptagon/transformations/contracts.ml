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

(* Inline code in contracts, collect assume/guarantee of subnodes *)

(* To be done before "completion" and "switch" transformations *)

open Misc
open Names
open Idents
open Heptagon
open Hept_utils
open Hept_mapfold
open Initial
open Signature
open Types
open Linearity

(** v_acc is the new local vars which were in lower levels,
    eq_acc contains all the equations *)

let fresh = Idents.gen_var "contracts"

let not_exp e = mk_exp (mk_op_app (Efun pnot) [e]) tbool ~linearity:Ltop

let (&&&) e1 e2 = mk_exp (mk_op_app (Efun pand) [e1;e2]) tbool ~linearity:Ltop
let (|||) e1 e2 = mk_exp (mk_op_app (Efun por) [e1;e2]) tbool ~linearity:Ltop

let (=>) e1 e2 = (not_exp e1) ||| e2

let var_exp v = mk_exp (Evar v) tbool ~linearity:Ltop

let true_exp = mk_exp (Econst (mk_static_bool true)) tbool ~linearity:Ltop

let mk_unique_node nd =
  let mk_bind vd =
    let id = fresh (Idents.name vd.v_ident) in
    (vd.v_ident, { vd with v_ident = id; v_clock = Clocks.fresh_clock () }) in
  let subst =
    List.fold_left
      (fun subst vd ->
         let id, vd = mk_bind vd in
         Env.add id vd.v_ident subst)
      Env.empty
      (nd.n_input @ nd.n_output) in

  let subst_var_ident _funs subst v =
    try
      let v = Env.find v subst in
      v, subst
    with Not_found ->
      Format.printf "Contracts: subst for ident %a not found@\n" Global_printer.print_ident v;
      raise Not_found
  in

  let subst_block funs subst b =
    let b_local, subst' =
      mapfold
        (fun subst vd ->
           let id, vd = mk_bind vd in
           vd, (Env.add id vd.v_ident subst))
        subst b.b_local in
    let b, _ = Hept_mapfold.block funs subst' b in
    { b with b_local = b_local }, subst
  in

  let subst_contract_block funs subst b =
    let b_local, subst' =
      mapfold
        (fun subst vd ->
           let id, vd = mk_bind vd in
           vd, (Env.add id vd.v_ident subst))
        subst b.b_local in
    let b, _ = Hept_mapfold.block funs subst' b in
    { b with b_local = b_local }, subst'
  in

  let subst_contract funs subst c =
    let c_block, subst' = subst_contract_block funs subst c.c_block in
    let c_assume, subst' = exp_it funs subst' c.c_assume in
    let c_objectives, _subst' = mapfold (objective_it funs) subst' c.c_objectives in
    let subst =
    List.fold_left
      (fun subst vd ->
         let id, vd = mk_bind vd in
         Env.add id vd.v_ident subst)
      subst c.c_controllables in
    let c_controllables, subst = mapfold (var_dec_it funs) subst c.c_controllables in
    let c_assume_loc = c.c_assume_loc in
    let c_enforce_loc = c.c_enforce_loc in
    { c_assume = c_assume;
      c_objectives = c_objectives;
      c_assume_loc = c_assume_loc;
      c_enforce_loc = c_enforce_loc;
      c_block = c_block;
      c_controllables = c_controllables },
    subst in

  (* let funs = { defaults with *)
  (*                var_dec = subst_var_dec; *)
  (*                eqdesc = subst_eqdesc; *)
  (*                edesc = subst_edesc; } in *)
  let funs = { Hept_mapfold.defaults with
                 block = subst_block;
                 contract = subst_contract;
                 global_funs = { Global_mapfold.defaults with
                                   Global_mapfold.var_ident = subst_var_ident } } in
  fst (Hept_mapfold.node_dec funs subst nd)

let mk_unique_contract nd =
  let mk_bind vd =
    let id = fresh (Idents.name vd.v_ident) in
    (vd.v_ident, { vd with v_ident = id; v_clock = Clocks.fresh_clock () }) in

  let c_local =
    match nd.n_contract with
      None -> []
    | Some { c_block = b } -> b.b_local in

  let subst = List.map mk_bind (c_local @ nd.n_input @ nd.n_output) in

  let subst_var_dec _ () vd = (List.assoc vd.v_ident subst, ()) in

  let subst_edesc funs () ed =
    let ed, () = Hept_mapfold.edesc funs () ed in
    let find vn = (List.assoc vn subst).v_ident in
    (match ed with
      | Evar vn -> Evar (find vn)
      | Elast vn -> Elast (find vn)
      | Ewhen (e, cn, vn) -> Ewhen (e, cn, find vn)
      | Emerge (vn, e_l) -> Emerge (find vn, e_l)
      | _ -> ed), ()
  in

  let subst_eqdesc funs () eqd =
    let (eqd, ()) = Hept_mapfold.eqdesc funs () eqd in
    match eqd with
    | Eeq (pat, e) ->
        let rec subst_pat pat = match pat with
          | Evarpat vn -> Evarpat (try (List.assoc vn subst).v_ident
                                   with Not_found -> vn)
          | Etuplepat patl -> Etuplepat (List.map subst_pat patl) in
        (Eeq (subst_pat pat, e), ())
    | _ -> raise Errors.Fallback in

  let funs = { defaults with
                 var_dec = subst_var_dec;
                 eqdesc = subst_eqdesc;
                 edesc = subst_edesc; } in
  fst (Hept_mapfold.node_dec funs () nd)

let mk_vd_bool v = mk_var_dec ~last:(Last (Some (mk_static_bool true))) v tbool ~linearity:Ltop

let exp funs (env, newvars, newequs, cont_vars, contracts) exp =
  let exp, (env, newvars, newequs, cont_vars, contracts) =
    Hept_mapfold.exp funs (env, newvars, newequs, cont_vars, contracts) exp in
  match exp.e_desc with
  | Eapp ({ a_op = (Enode nn | Efun nn); } as op, argl, rso) ->
    begin try

      let add_reset eq = match rso with
        | None -> eq
        | Some x -> mk_equation (Ereset (mk_block [eq], x)) in

      let n = QualEnv.find nn env in
      let ni = mk_unique_node n in

      let ci = match ni.n_contract with
          None -> raise Not_found
        | Some c -> c in

      let static_subst =
        List.combine (List.map (fun p -> (local_qn p.p_name)) ni.n_params)
          op.a_params in

      (* Perform [static_exp] substitution. *)
      let ni =
        let apply_sexp_subst_sexp funs () sexp = match sexp.se_desc with
          | Svar s -> ((try List.assoc s static_subst
                        with Not_found -> sexp), ())
          | _ -> Global_mapfold.static_exp funs () sexp in

        let funs =
          { defaults with global_funs =
              { Global_mapfold.defaults with Global_mapfold.static_exp =
                  apply_sexp_subst_sexp; }; } in

        fst (Hept_mapfold.node_dec funs () ni) in

      (* equation "x = e" for inputs *)
      let mk_input_equ vd e = mk_equation (Eeq (Evarpat vd.v_ident, e)) in
      (* output expression "y" *)
      let mk_output_exp vd = mk_exp (Evar vd.v_ident) vd.v_type ~linearity:vd.v_linearity in

      (* equation "y = f(x)" *)
      let eq_app =
        let pat = match ni.n_output with
            [o] -> Evarpat(o.v_ident)
          | ol -> Etuplepat(List.map (fun o -> Evarpat(o.v_ident)) ol) in
        let v_argl =
          List.map
            (fun vd -> mk_exp (Evar vd.v_ident) vd.v_type ~linearity:vd.v_linearity)
            ni.n_input in
        mk_equation (Eeq (pat, { exp with e_desc = Eapp (op, v_argl, rso) })) in

      (* variables for assume and guarantee *)
      let v_a = fresh ((shortname nn) ^ "_assume") in
      let v_g = fresh ((shortname nn) ^ "_guarantee") in
      (* variable declarations for assume/guarantee *)
      let vd_a = mk_vd_bool v_a in
      let vd_g = mk_vd_bool v_g in

      (* Build an expression composed of every "enforce" objective of the contract *)
      let rec build_enforce o_list =
	match o_list with
	  [] -> true_exp
	| [o] -> o.o_exp
	| o :: l -> o.o_exp &&& (build_enforce l) in

      (* Currently, only the enforce part is used for modularity *)
      let enforce_exp =
	build_enforce
	  (List.filter (fun o -> o.o_kind = Obj_enforce) ci.c_objectives) in

      (* equations for assume/guarantee *)
      let eq_a = mk_equation (Eeq (Evarpat v_a, ci.c_assume)) in
      let eq_g = mk_equation (Eeq (Evarpat v_g, enforce_exp)) in


      let newvars = ni.n_input @ ci.c_block.b_local @ ni.n_output @ newvars
      and newequs =
        List.map2 mk_input_equ ni.n_input argl
        @ List.map add_reset ci.c_block.b_equs
        @ [ eq_app; eq_a; eq_g ]
        @ newequs
      and cont_vars = vd_a :: vd_g :: cont_vars
      and contracts = (vd_a,vd_g)::contracts in

      (* For clocking reason we cannot create 1-tuples. *)
      let res_e = match ni.n_output with
        | [o] -> mk_output_exp o
        | _ ->
            mk_exp (Eapp ({ op with a_op = Etuple; },
                          List.map mk_output_exp ni.n_output, None)) exp.e_ty
                   ~linearity:exp.e_linearity in

      (res_e, (env, newvars, newequs, cont_vars, contracts))

    with
      | Not_found ->
        exp, (env, newvars, newequs, cont_vars, contracts)
    end
  | _ -> exp, (env, newvars, newequs, cont_vars, contracts)

let block funs (env, newvars, newequs, cont_vars, contracts) blk =
  let (blk, (env, newvars', newequs', cont_vars', contracts')) =
    Hept_mapfold.block funs (env, [], [], [], contracts) blk in
  (* let defnames = List.fold_left (fun env v -> Env.add v.v_ident v env) blk.b_defnames newvars' in *)
  let defnames = List.fold_left
    (fun env v -> Env.add v.v_ident v env)
    blk.b_defnames cont_vars' in
  ({ blk with
    b_local = newvars' @ blk.b_local;
    b_equs = newequs' @ blk.b_equs;
    b_defnames = defnames;
   },
   (env, newvars, newequs, (cont_vars @ cont_vars'), contracts'))

let node_dec funs (env, newvars, newequs, cont_vars, contracts) nd =
  let nd, (env, newvars, newequs, _cont_vars, contracts) =
    Hept_mapfold.node_dec funs (env, newvars, newequs, cont_vars, contracts) nd in

  (* Build assume and guarantee parts from contract list (list of
     ident pairs (v_a,v_g)). Returns also a list of variable
     declarations. *)
  let rec build_contract contracts =
    match contracts with
      [] -> true_exp, true_exp, []
    | [(v_a,v_g)] ->
        let e_a = var_exp v_a.v_ident in
        let e_g = var_exp v_g.v_ident in
        (* assume part : e_a => e_g ; guarantee part : e_a *)
        (e_a => e_g), e_a, [v_a; v_g]
    | (v_a,v_g)::l ->
        let e_a_l,e_g_l,vd_l = build_contract l in
        let e_a = var_exp v_a.v_ident in
        let e_g = var_exp v_g.v_ident in
        ((e_a => e_g) &&& e_a_l), (e_a &&& e_g_l),
        (v_a :: v_g :: vd_l)
  in

  let assume_loc, enforce_loc, vd_contracts = build_contract contracts in
  let nc =
    match nd.n_contract, contracts with
      c,[] -> c
    | None,_::_ ->
        Some { c_assume = true_exp;
               c_objectives = [];
               c_assume_loc = assume_loc;
               c_enforce_loc = enforce_loc;
               c_controllables = [];
               c_block = mk_block ~stateful:false [] }
    | Some c,_::_ ->
        Some { c with
                 c_assume_loc = assume_loc;
                 c_enforce_loc = enforce_loc } in
  let nd =
    { nd with
        n_contract = nc;
        n_block =
        { nd.n_block with
            b_local = newvars @ vd_contracts @ nd.n_block.b_local;
            b_equs = newequs @ nd.n_block.b_equs } } in
  let env = QualEnv.add nd.n_name nd env in
   nd, (env, [], [], [], [])

let program p =
  let funs =
    { defaults with exp = exp; block = block; node_dec = node_dec; eq = eq; } in
  let (p, (_, newvars, newequs, _cont_vars, contracts)) =
    Hept_mapfold.program funs (QualEnv.empty, [], [], [], []) p in
  assert (newvars = []);
  assert (newequs = []);
  assert (contracts = []);
  p
