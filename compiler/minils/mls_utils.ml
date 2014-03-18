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
open Minils
open Mls_mapfold
open Mls_printer
open Location
open Names
open Idents
open Signature
open Types
open Clocks

(** Error Kind *)
type err_kind = | Enot_static_exp

let err_message exp ?(loc=exp.e_loc) = function
  | Enot_static_exp ->
      Format.eprintf "%aThe expression %a should be a static_exp.@."
        print_location loc
        print_exp exp;
      raise Errors.Error

let static_exp_of_exp e =
  match e.e_desc with
    | Eextvalue w -> (match w.w_desc with
      | Wconst se -> se
      | _ -> err_message e Enot_static_exp)
    | _ -> err_message e Enot_static_exp

let rec ident_of_extvalue w = match w.w_desc with
  | Wvar x -> Some x
  | Wfield(w, _) -> ident_of_extvalue w
  | Wwhen(w, _, _) -> ident_of_extvalue w
  | Wconst _ -> None
  | Wreinit (_, w) -> ident_of_extvalue w

(** @return the list of bounds of an array type*)
let rec bounds_list ty =
  match Modules.unalias_type ty with
    | Tarray(ty, n) -> n::(bounds_list ty)
    | _ -> []

(** @return the [var_dec] object corresponding to the name [n]
    in a list of [var_dec]. *)
let rec vd_find n = function
  | [] -> (*Format.eprintf "Not found var %s@." (name n);*) raise Not_found
  | vd::l ->
      if vd.v_ident = n then vd else vd_find n l

(** @return whether an object of name [n] belongs to
    a list of [var_dec]. *)
let rec vd_mem n = function
  | [] -> false
  | vd::l -> vd.v_ident = n || (vd_mem n l)


(** @return whether [ty] corresponds to a record type. *)
let is_record_type ty = match ty with
  | Tid n ->
      (match Modules.find_type n with
        | Tstruct _ -> true
        | _ -> false)
  | _ -> false

let is_op = function
  | { qual = Pervasives; name = _ } -> true | _ -> false

module Vars =
struct
  let add x acc = if List.mem x acc then acc else x :: acc

  let rec vars_pat acc = function
    | Evarpat x -> x :: acc
    | Etuplepat pat_list -> List.fold_left vars_pat acc pat_list

  let def acc { eq_lhs = pat } = vars_pat acc pat

  let rec vars_ck acc = function
    | Clocks.Con(ck, _, n) -> vars_ck (add n acc) ck
    | Clocks.Cbase | Cvar { contents = Cindex _ } -> acc
    | Cvar { contents = Clink ck } -> vars_ck acc ck

  let rec vars_ct acc = function
    | Ck ck -> vars_ck acc ck
    | Cprod c_l -> List.fold_left vars_ct acc c_l

  let read_extvalue read_funs (is_left, acc_init) w =
    (* recursive call *)
    let _,(_, acc) = Mls_mapfold.extvalue read_funs (is_left, acc_init) w in
    let acc = match w.w_desc with
      | Wvar x | Wwhen(_, _, x) ->
          add x acc
      | _ -> acc
    in
      w, (is_left, vars_ck acc w.w_ck)

  let read_exp read_funs (is_left, acc_init) e =
    (* recursive call *)
    let _,(_, acc) = Mls_mapfold.exp read_funs (is_left, acc_init) e in

    (* special cases *)
    let acc = match e.e_desc with
      | Emerge(x,_)
      | Eapp(_, _, Some x) | Eiterator (_, _, _, _, _, Some x) ->
          add x acc
      | Efby(_, e) ->
          if is_left then
            (* do not consider variables to the right
               of the fby, only clocks*)
            vars_ck acc_init e.w_ck
          else acc
      | _ -> acc
    in
    e, (is_left, vars_ct acc e.e_ct)

  let read_exp is_left acc e =
    let _, (_, acc) =
      Mls_mapfold.exp_it
        { Mls_mapfold.defaults with
          Mls_mapfold.exp = read_exp;
          Mls_mapfold.extvalue = read_extvalue }
        (is_left, acc) e in
    acc

  let read_extvalue is_left acc e =
    let _, (_, acc) =
      Mls_mapfold.extvalue_it
        { Mls_mapfold.defaults with Mls_mapfold.extvalue = read_extvalue }
        (is_left, acc) e in
    acc

  let rec remove x = function
    | [] -> []
    | y :: l -> if x = y then l else y :: remove x l

  let read is_left { eq_lhs = pat; eq_rhs = e } = match pat, e.e_desc with
    |  Evarpat(n), Efby(_, e1) ->
         if is_left
         then remove n (read_extvalue is_left [] e1)
         else read_extvalue is_left [] e1
    | _ -> read_exp is_left [] e

  let rec is_fby e = match e.e_desc with
    | Ewhen (e, _, _) -> is_fby e
    | Efby (_, _) -> true
    | _ -> false

  let antidep { eq_rhs = e } = is_fby e

  let clock eq = eq.eq_base_ck

  let head ck =
    let rec headrec ck l =
      match ck with
        | Clocks.Cbase
        | Cvar { contents = Cindex _ } -> l
        | Clocks.Con(ck, _, n) -> headrec ck (n :: l)
        | Cvar { contents = Clink ck } -> headrec ck l
    in
    headrec ck []

  (** Returns a list of memory vars (x in x = v fby e)
      appearing in an equation. *)
  let rec memory_vars ({ eq_lhs = _; eq_rhs = e } as eq) = match e.e_desc with
    | Efby(_, _) -> def [] eq
    | Ewhen(e,_,_) -> memory_vars {eq with eq_rhs = e}
    | _ -> []

  let linear_read e =
    let extvalue funs acc w = match w.w_desc with
      | Wvar x ->
        let w, acc = Mls_mapfold.extvalue funs acc w in
        let acc =
          (match w.w_linearity with
            | Linearity.Lat _ -> add x acc
            | _ -> acc)
        in
        w, acc
      | _ -> Mls_mapfold.extvalue funs acc w
    in
    let funs = { Mls_mapfold.defaults with extvalue = extvalue } in
    let _, acc = Mls_mapfold.exp_it funs [] e in
    acc
end

(* Assumes normal form, all fby are solo rhs or inside a when *)
let node_memory_vars n =
  let rec eq funs acc ({ eq_lhs = pat; eq_rhs = e } as equ) =
    match pat, e.e_desc with
    | Evarpat _, Ewhen(e,_,_) -> eq funs acc {equ with eq_rhs = e}
    | Evarpat x, Efby(_, _) ->
        let acc = (x, e.e_ty) :: acc in
        equ, acc
    | _, _ -> equ, acc
  in
  let funs = { Mls_mapfold.defaults with eq = eq } in
  let _, acc = node_dec_it funs [] n in
    acc


(* data-flow dependences. pre-dependences are discarded *)
module DataFlowDep = Dep.Make
  (struct
     type equation = eq
     let read eq = Vars.read true eq
     let linear_read eq = Vars.linear_read eq.eq_rhs
     let def = Vars.def
     let antidep = Vars.antidep
   end)

(* all dependences between variables *)
module AllDep = Dep.Make
  (struct
     type equation = eq
     let read eq = Vars.read false eq
     let linear_read eq = Vars.linear_read eq.eq_rhs
     let def = Vars.def
     let antidep _ = false
   end)

let eq_find id = List.find (fun eq -> List.mem id (Vars.def [] eq))

let ident_list_of_pat pat =
  let rec f acc pat = match pat with
    | Evarpat id -> id::acc
    | Etuplepat pat_l -> List.fold_left f acc pat_l
  in
  List.rev (f [] pat)

let find_var_node nd x =
  try vd_find x nd.n_input with Not_found ->
  try vd_find x nd.n_output with Not_found ->
  vd_find x nd.n_local

let remove_eqs_from_node nd ids =
  let walk_vd vd vd_list = if IdentSet.mem vd.v_ident ids then vd_list else vd :: vd_list in
  let walk_eq eq eq_list =
    let defs = ident_list_of_pat eq.eq_lhs in
    if (not eq.eq_unsafe) && List.for_all (fun v -> IdentSet.mem v ids) defs
    then eq_list
    else eq :: eq_list
  in
  let vd_list = List.fold_right walk_vd nd.n_local [] in
  let eq_list = List.fold_right walk_eq nd.n_equs [] in
  { nd with n_local = vd_list; n_equs = eq_list; }

let args_of_var_decs =
 List.map
   (fun vd -> Signature.mk_arg (Some (Idents.source_name vd.v_ident))
                               vd.v_type (Linearity.check_linearity vd.v_linearity)
                               (ck_to_sck (Clocks.ck_repr vd.v_clock)))

let signature_of_node n =
  { node_inputs = args_of_var_decs n.n_input;
    node_outputs  = args_of_var_decs n.n_output;
    node_stateful = n.n_stateful;
    node_unsafe = n.n_unsafe;
    node_params = n.n_params;
    node_param_constraints = n.n_param_constraints;
    node_external = false;
    node_loc = n.n_loc }
