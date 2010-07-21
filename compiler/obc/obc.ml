(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* Object code internal representation *)

open Misc
open Names
open Ident
open Types
open Signature
open Location

type class_name = name
type instance_name = longname
type obj_name = name
type op_name = longname

type type_dec =
    { t_name : name;
      t_desc : tdesc;
      t_loc : location }

and tdesc =
  | Type_abs
  | Type_enum of name list
  | Type_struct of structure

type const_dec = {
  c_name : name;
  c_value : static_exp;
  c_type : ty;
  c_loc : location }

type lhs = { l_desc : lhs_desc; l_ty : ty; l_loc : location }

and lhs_desc =
  | Lvar of var_ident
  | Lmem of var_ident
  | Lfield of lhs * field_name
  | Larray of lhs * exp

and exp = { e_desc : exp_desc; e_ty : ty; e_loc : location }

and exp_desc =
  | Elhs of lhs
  | Econst of static_exp
  | Eop of op_name * exp list
  | Estruct of type_name * (field_name * exp) list
  | Earray of exp list

type obj_call =
  | Oobj of obj_name
  | Oarray of obj_name * lhs

type method_name =
  | Mreset
  | Mstep
  | Mmethod of name

type act =
  | Aassgn of lhs * exp
  | Acall of lhs list * obj_call * method_name * exp list
  | Acase of exp * (constructor_name * block) list
  | Afor of var_ident * static_exp * static_exp * block

and block = act list

type var_dec =
    { v_ident : var_ident;
      v_type : ty; (* TODO should be here, v_controllable : bool*)
      v_loc : location }

type obj_dec =
    { o_name : obj_name;
      o_class : instance_name;
      o_size : static_exp option;
      o_loc : location }

type method_def =
    { m_name : method_name;
      m_inputs : var_dec list;
      m_outputs : var_dec list;
      m_locals : var_dec list;
      m_body : block; }

type class_def =
    { cd_name : class_name;
      cd_mems : var_dec list;
      cd_objs  : obj_dec list;
      cd_params : param list;
      cd_methods: method_def list;
      cd_loc : location }

type program =
    { p_modname : name;
      p_opened : name list;
      p_types : type_dec list;
      p_consts : const_dec list;
      p_defs  : class_def list }

let mk_var_dec ?(loc=no_location) name ty =
  { v_ident = name; v_type = ty; v_loc = loc }

let mk_exp ?(ty=invalid_type) ?(loc=no_location) desc =
  { e_desc = desc; e_ty = ty; e_loc = loc }

let mk_lhs ?(ty=invalid_type) ?(loc=no_location) desc =
  { l_desc = desc; l_ty = ty; l_loc = loc }

let mk_lhs_exp ?(ty=invalid_type) desc =
  let lhs = mk_lhs ~ty:ty desc in
    mk_exp ~ty:ty (Elhs lhs)

let mk_evar id =
  mk_exp (Elhs (mk_lhs (Lvar id)))

let rec var_name x =
  match x.l_desc with
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
  | [] -> Format.printf "Not found var %s\n" (name n); raise Not_found
  | vd::l ->
      if vd.v_ident = n then vd else vd_find n l

let lhs_of_exp e = match e.e_desc with
  | Elhs l -> l
  | _ -> assert false

let find_step_method cd =
  List.find (fun m -> m.m_name = Mstep) cd.cd_methods
let find_reset_method cd =
  List.find (fun m -> m.m_name = Mreset) cd.cd_methods

let obj_call_name o =
  match o with
    | Oobj obj
    | Oarray (obj, _) -> obj

