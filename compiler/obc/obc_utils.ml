(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Names
open Idents
open Location
open Misc
open Types
open Obc
open Obc_mapfold
open Global_mapfold

let mk_var_dec ?(loc=no_location) ?(mut=false) ident ty =
  { v_ident = ident; v_type = ty; v_mutable = mut; v_loc = loc }

let mk_exp ?(loc=no_location) ty desc =
  { e_desc = desc; e_ty = ty; e_loc = loc }

let mk_exp_int ?(loc=no_location) desc =
  { e_desc = desc; e_ty = Initial.tint; e_loc = loc }

let mk_exp_bool ?(loc=no_location) desc =
  { e_desc = desc; e_ty = Initial.tbool; e_loc = loc }

let mk_pattern ?(loc=no_location) ty desc =
  { pat_desc = desc; pat_ty = ty; pat_loc = loc }

let mk_pattern_int ?(loc=no_location) desc =
  { pat_desc = desc; pat_ty = Initial.tint; pat_loc = loc }

let mk_pattern_exp ty desc =
  let pat = mk_pattern ty desc in
    mk_exp ty (Epattern pat)

let mk_evar ty id =
  mk_exp ty (Epattern (mk_pattern ty (Lvar id)))

let mk_evar_int id =
  mk_exp Initial.tint (Epattern (mk_pattern Initial.tint (Lvar id)))

let mk_block ?(locals=[]) eq_list =
  { b_locals = locals;
    b_body = eq_list }

let mk_ifthenelse cond true_act false_act =
  Acase (cond, [ ptrue, mk_block [true_act]; pfalse, mk_block [false_act] ])

let rec var_name x =
  match x.pat_desc with
    | Lvar x -> x
    | Lmem x -> x
    | Lfield(x,_) -> var_name x
    | Larray(l, _) -> var_name l

(** Returns whether an object of name n belongs to
    a list of var_dec. *)
let rec vd_mem n = function
  | [] -> false
  | vd::l -> vd.v_ident = n or (vd_mem n l)

(** Returns the var_dec object corresponding to the name n
    in a list of var_dec. *)
let rec vd_find n = function
  | [] -> Format.eprintf "Not found var %s@." (name n); raise Not_found
  | vd::l ->
      if vd.v_ident = n then vd else vd_find n l

(** Returns the type of a [var_dec list] *)
let vd_list_to_type vd_l = match vd_l with
  | [] -> Types.Tunit
  | [vd] -> vd.v_type
  | _ -> Tprod (List.map (fun vd -> vd.v_type) vd_l)

let pattern_list_to_type p_l = match p_l with
  | [] -> Types.Tunit
  | [p] -> p.pat_ty
  | _ -> Tprod (List.map (fun p -> p.pat_ty) p_l)

let pattern_of_exp e = match e.e_desc with
  | Epattern l -> l
  | _ -> assert false

let find_step_method cd =
  List.find (fun m -> m.m_name = Mstep) cd.cd_methods
let find_reset_method cd =
  List.find (fun m -> m.m_name = Mreset) cd.cd_methods

let obj_ref_name o =
  match o with
    | Oobj obj
    | Oarray (obj, _) -> obj

(** Input a block [b] and remove all calls to [Reset] method from it *)
let remove_resets b =
  let block funs _ b =
    let b,_ = Obc_mapfold.block funs () b in
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
                        static_exp_desc = deps_static_exp_desc; };
      lhsdesc = deps_lhsdesc;
      edesc = deps_edesc;
      act = deps_act;
      obj_dec = deps_obj_dec;
    } in
    let (_, deps) = Obc_mapfold.program funs ModulSet.empty p in
    ModulSet.remove p.p_modname deps
end

(** Creates a new for loop. Expects the size of the iteration
    and the body as a function of the variable iterating. *)
let fresh_for pass down up body =
  let i = Idents.gen_var pass "i" in
  let id = mk_var_dec i Initial.tint in
  let ei = mk_evar_int i in
    Afor (id, down, up, mk_block (body ei))

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
