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

open Names
open Idents
open Minils
open Mls_utils
open Types
open Clocks

(*
  Help tomato by inlining extended values.

  1. Create an environment mapping x to w for each equation of the form "x = w" ;

  2. Traverse the AST, replacing each use of x by its definition ;

  3. Compute potential new formed extended values, e.g. when y = 1 + x becomes y = 1 + w ;

  4. If no new extended value was formed, stop ; else, go back to 1.
*)


let gather_extvalues_node nd =
  let ty_env =
    let add env vd = Env.add vd.v_ident vd.v_linearity env in
    let add_l env vd_list = List.fold_left add env vd_list in
    let env = add_l (add_l (add_l Env.empty nd.n_output) nd.n_local) nd.n_input in
    match nd.n_contract with
    | None -> env
    | Some c -> add_l (add_l env c.c_controllables) c.c_local
  in

  (* Check for implicit cast from linear to non-linear type *)
  let is_linear w =
    let rec var_of_extvalue w = match w.w_desc with
      | Wvar x -> Some x
      | Wfield(w, _) -> var_of_extvalue w
      | Wwhen(w, _, _) -> var_of_extvalue w
      | Wconst _ -> None
      | Wreinit (_, w) -> var_of_extvalue w
    in
    match var_of_extvalue w with
      | Some x ->
        let lin = Env.find x ty_env in
        Linearity.is_linear lin
      | _ -> false
  in

  let inlinable w = match w.w_desc with
    | Wconst { se_desc = Sarray _ | Sarray_power _ } -> false
    | _ -> true
  in

  let gather_extvalues_eq _ env eq =
    let env = match eq.eq_lhs, eq.eq_rhs.e_desc with
      | Evarpat x, Eextvalue w when not (is_linear w) && inlinable w -> Env.add x w env
      | _ -> env
    in
    eq, env
  in

  let funs = { Mls_mapfold.defaults with Mls_mapfold.eq = gather_extvalues_eq; } in
  let _, env = Mls_mapfold.node_dec funs Env.empty nd in
  env

let inline_extvalue_node env nd =
  let find_sampler env x = match (Env.find x env).w_desc with
    | Wvar x -> x
    | _ -> raise Not_found
  in

  let inline_extvalue_desc env funs () w_d =
    let w_d, () = Mls_mapfold.extvalue_desc funs () w_d in
    (try match w_d with
      | Wvar x -> ((Env.find x env).w_desc)
      | Wwhen (w, c, x) -> Wwhen (w, c, find_sampler env x)
      | _ -> w_d
     with Not_found -> w_d), ()
  in

  let inline_edesc env funs () e_d =
    let e_d', () = Mls_mapfold.edesc funs () e_d in
    (* Format.eprintf "From %a to %a@." print_exp_desc e_d print_exp_desc e_d'; *)
    let e_d = e_d' in
    (try match e_d with
      | Emerge (x, cl) -> Emerge (find_sampler env x, cl)
      | Ewhen (e, v, x) -> Ewhen (e, v, find_sampler env x)
      | Eapp (op, args, Some x) -> Eapp (op, args, Some (find_sampler env x))
      | _ -> e_d
     with Not_found -> e_d), ()
  in

  let inline_ck env funs () ck =
    let ck, () = Global_mapfold.ck funs () ck in
    (try match ck with
      | Con (ck, cn, x) -> Con (ck, cn, find_sampler env x)
      | _ -> ck
     with Not_found -> ck), ()
  in

  let env =
    let funs =
      { Mls_mapfold.defaults with
        Mls_mapfold.extvalue_desc = inline_extvalue_desc env;
        Mls_mapfold.edesc = inline_edesc env;
        Mls_mapfold.global_funs =
          { Global_mapfold.defaults with
            Global_mapfold.ck = inline_ck env; }; } in

    let tclose x w new_env =
      let rec fix w =
        let w', () = Mls_mapfold.extvalue funs () w in
        if Mls_compare.extvalue_compare w w' = 0 then w else fix w'
      in
      Env.add x (fix w) new_env
    in
    Env.fold tclose env Env.empty
  in

  let funs =
    {
      Mls_mapfold.defaults with
        Mls_mapfold.extvalue_desc = inline_extvalue_desc env;
        Mls_mapfold.edesc = inline_edesc env;
        Mls_mapfold.global_funs =
        { Global_mapfold.defaults with
          Global_mapfold.ck = inline_ck env; };
    }
  in

  let nd, () = Mls_mapfold.node_dec funs () nd in
  nd

let form_new_extvalue_node nd =
  let rec form_new_extvalue e =
    try
      let se = form_new_const e in
      mk_extvalue
        ~ty:e.e_ty ~linearity:e.e_linearity
        ~clock:(Clocks.first_ck e.e_ct) ~loc:e.e_loc (Wconst se)
    with Errors.Fallback ->
      let w_d = match e.e_desc with
        | Eextvalue w -> w.w_desc
        | Ewhen (e, v, x) -> Wwhen (form_new_extvalue e, v, x)
        | _ -> raise Errors.Fallback
      in
      mk_extvalue ~ty:e.e_ty ~linearity:e.e_linearity
        ~clock:(Clocks.first_ck e.e_ct) ~loc:e.e_loc w_d

  and form_new_const e =
    let se_d = match e.e_desc with
      | Eextvalue { w_desc = Wconst c; } -> c.se_desc

      (* | Eextvalue { w_desc = Wvar n; } -> *)
      (*   (try Svar (Q (qualify_const local_const (ToQ n))) *)
      (*    with Error.ScopingError _ -> raise Errors.Fallback) *)

      | Eapp ({ a_op = Efun ({ qual = Names.Pervasives; } as funn); }, w_list, None) ->
        Sop (funn, form_new_consts w_list)

      | Eapp ({ a_op = Earray_fill; a_params = n_list; }, [w], None) ->
        Sarray_power (form_new_const_w w, n_list)

      | Eapp ({ a_op = Earray; }, w_list, None) ->
        Sarray (form_new_consts w_list)

      | Estruct w_list ->
        Srecord (List.map (fun (f, w) -> f, form_new_const_w w) w_list)

      | _ -> raise Errors.Fallback
    in
    mk_static_exp ~loc:e.e_loc e.e_ty se_d

  and form_new_consts w_list = List.map form_new_const_w w_list

  and form_new_const_w w =
    let mk_exp w =
      mk_exp w.w_ck w.w_ty ~linearity:w.w_linearity ~ct:(Ck w.w_ck) (Eextvalue w) in
    form_new_const (mk_exp w)

  and form_new_extvalue_eq _ n eq = match eq.eq_rhs.e_desc with
    | Eextvalue _ -> (eq, n)
    | _ ->
      try
        let w = form_new_extvalue eq.eq_rhs in
        let e = { eq.eq_rhs with e_desc = Eextvalue w; } in
        { eq with eq_rhs = e; }, n + 1
      with Errors.Fallback ->
        eq, n
  in

  let funs = { Mls_mapfold.defaults with Mls_mapfold.eq = form_new_extvalue_eq; } in
  let nd, n = Mls_mapfold.node_dec funs 0 nd in
  nd, n > 0

let compute_needed nd =
  let compute_needed_edesc funs ids e_d =
    let e_d, ids = Mls_mapfold.edesc funs ids e_d in
    e_d,
    (match e_d with
      | Emerge (x, _) -> IdentSet.add x ids
      | Ewhen (_, _, x) -> IdentSet.add x ids
      | Eapp (_, _, Some x) -> IdentSet.add x ids
      | _ -> ids)

  and compute_needed_extvalue_desc funs ids w_d =
    let w_d, ids = Mls_mapfold.extvalue_desc funs ids w_d in
    w_d,
    (match w_d with
      | Wwhen (_, _, x) -> IdentSet.add x ids
      | _ -> ids)

  and compute_needed_node funs ids nd =
    let nd, ids = Mls_mapfold.node_dec funs ids nd in
    nd, (List.fold_left (fun ids v -> IdentSet.add v.v_ident ids) ids nd.n_output) in

  let funs =
    { Mls_mapfold.defaults with
      Mls_mapfold.node_dec = compute_needed_node;
      Mls_mapfold.extvalue_desc = compute_needed_extvalue_desc;
      Mls_mapfold.edesc = compute_needed_edesc; } in
  snd (Mls_mapfold.node_dec_it funs IdentSet.empty nd)

let id_set_of_env nd env =
  let needed = compute_needed nd in
  let add id _ ids = if IdentSet.mem id needed then ids else IdentSet.add id ids in
  Env.fold add env IdentSet.empty

let rec node funs () nd =
  let env = gather_extvalues_node nd in
  (* Format.eprintf "Env:@\n"; *)
  (* Env.iter (fun k w -> Format.eprintf "  %a => %a@\n" print_ident k print_extvalue w) env; *)
  (* Format.eprintf "@."; *)
  let nd = inline_extvalue_node env nd in
  let nd = remove_eqs_from_node nd (id_set_of_env nd env) in
  let nd, changed = form_new_extvalue_node nd in
  if changed then node funs () nd else (nd, ())

let program program =
  let funs = { Mls_mapfold.defaults with Mls_mapfold.node_dec = node; } in
  let program, () = Mls_mapfold.program funs () program in
  program
