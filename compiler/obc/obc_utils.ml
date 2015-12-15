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
open Location
open Types
open Linearity
open Obc
open Obc_mapfold
open Global_mapfold

let mk_var_dec ?(loc=no_location) ?(linearity = Ltop) ?(mut=false) ?(alias=false) ident ty =
  { v_ident = ident; v_type = ty; v_linearity = linearity;
    v_alias = alias; v_mutable = mut; v_loc = loc }

let mk_ext_value ?(loc=no_location) ty desc =
  { w_desc = desc; w_ty = ty; w_loc = loc; }

let mk_ext_value_int ?(loc=no_location) desc =
  mk_ext_value ~loc:loc Initial.tint desc

let mk_ext_value_bool ?(loc=no_location) desc =
  mk_ext_value ~loc:loc Initial.tbool desc

let mk_exp ?(loc=no_location) ty desc =
  { e_desc = desc; e_ty = ty; e_loc = loc }

let mk_exp_int ?(loc=no_location) desc =
  mk_exp ~loc:loc Initial.tint desc

let mk_exp_static_int ?(loc=no_location) se =
  mk_exp_int ~loc:loc (Eextvalue (mk_ext_value_int (Wconst se)))

let mk_exp_const_int ?(loc=no_location) i =
  mk_exp_static_int ~loc:loc (Initial.mk_static_int i)

let mk_exp_bool ?(loc=no_location) desc =
  { e_desc = desc; e_ty = Initial.tbool; e_loc = loc }

let mk_pattern ?(loc=no_location) ty desc =
  { pat_desc = desc; pat_ty = ty; pat_loc = loc }

let mk_pattern_int ?(loc=no_location) desc =
  { pat_desc = desc; pat_ty = Initial.tint; pat_loc = loc }

let mk_ext_value_exp ty desc =
  let w = mk_ext_value ty desc in
  mk_exp ty (Eextvalue w)

let mk_ext_value_exp_int desc = mk_ext_value_exp Initial.tint desc

let mk_ext_value_exp_bool desc = mk_ext_value_exp Initial.tbool desc

let mk_ext_value_exp_static ty sed = mk_ext_value_exp ty (Wconst sed)

let mk_ext_value_const_int i = mk_ext_value Initial.tint (Wconst (Initial.mk_static_int i))

let mk_evar ty id =
  mk_ext_value_exp ty (Wvar id)

let mk_evar_int id =
  mk_evar Initial.tint id

let mk_block ?(locals=[]) eq_list =
  { b_locals = locals;
    b_body = eq_list }

let mk_ifthenelse cond true_act false_act =
  Acase (cond, [ Initial.ptrue, mk_block true_act; Initial.pfalse, mk_block false_act ])

let mk_if cond true_act =
  Acase (cond, [Initial.ptrue, mk_block true_act])

let rec var_name x =
  match x.pat_desc with
    | Obc.Lvar x -> x
    | Lmem x -> x
    | Lfield(x,_) -> var_name x
    | Larray(l, _) -> var_name l

(** Returns whether an object of name n belongs to
    a list of var_dec. *)
let rec vd_mem n = function
  | [] -> false
  | vd::l -> vd.v_ident = n || (vd_mem n l)

(** Returns the var_dec object corresponding to the name n
    in a list of var_dec. *)
let rec vd_find n = function
  | [] -> Format.eprintf "Not found var %s@." (name n); raise Not_found
  | vd::l ->
      if vd.v_ident = n then vd else vd_find n l

(** Returns the type of a [var_dec list] *)
let vd_list_to_type vd_l = match vd_l with
  | [vd] -> vd.v_type
  | _ -> Tprod (List.map (fun vd -> vd.v_type) vd_l)

let pattern_list_to_type p_l = match p_l with
  | [p] -> p.pat_ty
  | _ -> Tprod (List.map (fun p -> p.pat_ty) p_l)

let ext_value_of_exp e = match e.e_desc with
  | Eextvalue w -> w
  | _ -> assert false

let find_step_method cd =
  List.find (fun m -> m.m_name = Mstep) cd.cd_methods
let find_reset_method cd =
  List.find (fun m -> m.m_name = Mreset) cd.cd_methods

let replace_step_method st cd =
  let f md = if md.m_name = Mstep then st else md in
    { cd with cd_methods = List.map f cd.cd_methods }

let obj_ref_name o =
  match o with
    | Oobj obj
    | Oarray (obj, _) -> obj

let rec find_obj o j = match j with
  | [] -> assert false
  | obj::j ->
    if o = obj.o_ident then
      Modules.find_value obj.o_class
    else
      find_obj o j

(** Input a block [b] and remove all calls to [Reset] method from it *)
let remove_resets b =
  let block funs () b =
    let b, () = Obc_mapfold.block funs () b in
    let is_not_reset a = match a with
      | Acall( _,_,Mreset,_) -> false
      | _ -> true
    in
    let b = { b with b_body = List.filter is_not_reset b.b_body } in
    b, ()
  in
  let funs = { Obc_mapfold.defaults with block = block } in
  let b,_ = block_it funs () b in
  b


module Deps =
struct

  let deps_longname deps qn = match qn.qual with
    | Module _ | QualModule _ -> ModulSet.add qn.qual deps
    | _ -> deps

  let deps_ty _ deps ty = match ty with
    | Tid ln -> ty, deps_longname deps ln
    | _ -> raise Errors.Fallback

  let deps_static_exp_desc funs deps sedesc =
    let (sedesc, deps) = Global_mapfold.static_exp_desc funs deps sedesc in
    match sedesc with
      | Svar ln -> (sedesc, deps_longname deps ln)
      | Sconstructor ln -> (sedesc, deps_longname deps ln)
      | Srecord fnel ->
        let add deps (ln, _) = deps_longname deps ln in
        (sedesc, List.fold_left add deps fnel)
      | Sop (ln, _) -> (sedesc, deps_longname deps ln)
      | _ -> raise Errors.Fallback

  let deps_lhsdesc funs deps ldesc =
    let (ldesc, deps) = Obc_mapfold.lhsdesc funs deps ldesc in
    match ldesc with
      | Lfield (_, ln) -> (ldesc, deps_longname deps ln)
      | _ -> raise Errors.Fallback

  let deps_edesc funs deps edesc =
    let (edesc, deps) = Obc_mapfold.edesc funs deps edesc in
    match edesc with
      | Eop (ln, _) -> (edesc, deps_longname deps ln)
      | Estruct (ln, fnel) ->
        let add deps (ln, _) = deps_longname deps ln in
        (edesc, List.fold_left add (deps_longname deps ln) fnel)
      | _ -> raise Errors.Fallback

  let deps_act funs deps act =
    let (act, deps) = Obc_mapfold.act funs deps act in
    match act with
      | Acase (_, cbl) ->
        let add deps (ln, _) = deps_longname deps ln in
        (act, List.fold_left add deps cbl)
      | _ -> raise Errors.Fallback

  let deps_obj_dec funs deps od =
    let (od, deps) = Obc_mapfold.obj_dec funs deps od in
    (od, deps_longname deps od.o_class)

  let deps_program p =
    let funs = { Obc_mapfold.defaults with
      global_funs = { Global_mapfold.defaults with
                        static_exp_desc = deps_static_exp_desc;
                        ty = deps_ty };
      lhsdesc = deps_lhsdesc;
      edesc = deps_edesc;
      act = deps_act;
      obj_dec = deps_obj_dec;
    } in
    let (_, deps) = Obc_mapfold.program funs ModulSet.empty p in
    ModulSet.remove p.p_modname deps

  let deps_interface i =
    let funs = { Obc_mapfold.defaults with
      global_funs = { Global_mapfold.defaults with
                        static_exp_desc = deps_static_exp_desc;
                        ty = deps_ty };
    } in
    let (_, deps) = Obc_mapfold.interface funs ModulSet.empty i in
    ModulSet.remove i.i_modname deps
end

(** Creates a new for loop. Expects the size of the iteration
    and the body as a function of the variable iterating. *)
let fresh_for pass down up body =
  let i = Idents.gen_var pass "i" in
  let id = mk_var_dec i Initial.tint in
  let ei = mk_evar_int i in
    Afor (id, down, up, mk_block (body ei))

(*
(** Creates the action copying [src] to [dest].*)
let rec copy_array pass dest src = match dest.l_ty with
  | Tarray (t, n) ->
      let copy i =
        let src_i = mk_pattern_exp t (Larray (src, i)) in
        let dest_i = mk_pattern t (Larray (dest, i)) in
          [copy_array dest_i src_i]
      in
        fresh_for pass (mk_static_int 0) n copy
  | _ ->
      Aassgn(dest, Epattern src)
*)

let program_types p =
  let add_type pd acc = match pd with
    | Ptype ty -> ty :: acc
    | _ -> acc
  in
    List.fold_right add_type p.p_desc []

let program_classes p =
  let add_class pd acc = match pd with
    | Pclass cd -> cd :: acc
    | _ -> acc
  in
    List.fold_right add_class p.p_desc []

let interface_types i =
  let add_type id acc = match id with
    | Itypedef ty -> ty :: acc
    | _ -> acc
  in
    List.fold_right add_type i.i_desc []

let rec ext_value_of_pattern patt =
  let desc = match patt.pat_desc with
    | Obc.Lvar id -> Wvar id
    | Lmem id -> Wmem id
    | Lfield (p, fn) -> Wfield (ext_value_of_pattern p, fn)
    | Larray (p, e) -> Warray (ext_value_of_pattern p, e) in
  mk_ext_value ~loc:patt.pat_loc patt.pat_ty desc

let exp_of_pattern patt =
  let w = ext_value_of_pattern patt in
  mk_exp w.w_ty (Eextvalue w)
