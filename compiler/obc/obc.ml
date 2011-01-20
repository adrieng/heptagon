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
open Idents
open Types
open Signature
open Location

type class_name = qualname
type op_name = qualname
type obj_ident = var_ident


type type_dec =
    { t_name : type_name;
      t_desc : tdesc;
      t_loc : location }

and tdesc =
  | Type_abs
  | Type_alias of ty
  | Type_enum of constructor_name list
  | Type_struct of structure

type const_dec = {
  c_name : qualname;
  c_value : static_exp;
  c_type : ty;
  c_loc : location }

type pattern = { pat_desc : pat_desc; pat_ty : ty; pat_loc : location }

and pat_desc =
  | Lvar of var_ident
  | Lmem of var_ident
  | Lfield of pattern * field_name
  | Larray of pattern * exp

and exp = { e_desc : exp_desc; e_ty : ty; e_loc : location }

and exp_desc =
  | Elhs of pattern
  | Econst of static_exp
  | Eop of op_name * exp list
  | Estruct of type_name * (field_name * exp) list
  | Earray of exp list
  | Ebang of exp

type obj_ref =
  | Oobj of obj_ident
  | Oarray of obj_ident * pattern

type method_name =
  | Mreset
  | Mstep

type act =
  | Aassgn of pattern * exp
  | Acall of pattern list * obj_ref * method_name * exp list
  | Aasync_call of async_t * pattern list * obj_ref * method_name * exp list
  | Acase of exp * (constructor_name * block) list
  | Afor of var_ident * static_exp * static_exp * block

and block =
    { b_locals : var_dec list;
      b_body : act list }

and var_dec =
    { v_ident : var_ident;
      v_type : ty; (* TODO GD should be here, v_controllable : bool *)
      v_loc : location }

type obj_dec =
    { o_ident : obj_ident;
      o_class : class_name;
      o_params : static_exp list;
      o_size : static_exp option; (** size of the array if the declaration is an array of obj *)
      o_loc : location }

type method_def =
    { m_name : method_name;
      m_inputs : var_dec list;
      m_outputs : var_dec list;
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

let mk_exp ?(ty=invalid_type) ?(loc=no_location) desc = (* TODO master :  remove the invalid_type *)
  { e_desc = desc; e_ty = ty; e_loc = loc }

let mk_lhs ?(ty=invalid_type) ?(loc=no_location) desc = (* TODO master :  remove the invalid_type *)
  { pat_desc = desc; pat_ty = ty; pat_loc = loc }

let mk_lhs_exp ?(ty=invalid_type) desc = (* TODO master :  remove the invalid_type *)
  let lhs = mk_lhs ~ty:ty desc in
    mk_exp ~ty:ty (Elhs lhs)

let mk_evar id =
  mk_exp (Elhs (mk_lhs (Lvar id)))

let mk_block ?(locals=[]) eq_list =
  { b_locals = locals;
    b_body = eq_list }

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
  | _ -> Tprod (List.map (fun p -> p.p_type) p_l)

let lhs_of_exp e = match e.e_desc with
  | Elhs l -> l
  | _ -> assert false

let find_step_method cd =
  List.find (fun m -> m.m_name = Mstep) cd.cd_methods
let find_reset_method cd =
  List.find (fun m -> m.m_name = Mreset) cd.cd_methods

let obj_ref_name o =
  match o with
    | Oobj obj
    | Oarray (obj, _) -> obj

