(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* Object code internal representation *)

(** See the manual for the semantics of the language *)


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

and ext_value = { w_desc : ext_value_desc; w_ty : ty; w_loc : location; }

and ext_value_desc =
  | Wvar of var_ident
  | Wconst of static_exp
  | Wmem of var_ident
  | Wfield of ext_value * field_name
  | Warray of ext_value * exp

and exp = { e_desc : exp_desc; e_ty : ty; e_loc : location }

and exp_desc =
  | Eextvalue of ext_value
  | Eop of op_name * exp list
  | Estruct of type_name * (field_name * exp) list
  | Earray of exp list

type obj_ref =
  | Oobj of obj_ident
  | Oarray of obj_ident * pattern

type method_name =
  | Mreset
  | Mstep

type act =
  | Aassgn of pattern * exp
  | Aop of op_name * exp list
  | Acall of pattern list * obj_ref * method_name * exp list
  | Acase of exp * (constructor_name * block) list
  | Afor of var_dec * exp * exp * block
  | Ablock of block

and block =
    { b_locals : var_dec list;
      b_body : act list }

and var_dec =
    { v_ident : var_ident;
      v_type : ty;
      v_mutable : bool;
      v_loc : location }

type obj_dec =
    { o_ident : obj_ident;
      o_class : class_name;
      o_params : static_exp list;
      (** size of the array if the declaration is an array of obj *)
      o_size : static_exp option;
      o_loc : location }

type method_def =
    { m_name : method_name;
      m_inputs : var_dec list;
      m_outputs : var_dec list;
      m_body : block; }

type class_def =
    { cd_name : class_name;
      (** when false, the class is a function with static parameters
          calling other functions with parameters *)
      cd_stateful : bool;
      cd_mems : var_dec list;
      cd_objs  : obj_dec list;
      cd_params : param list;
      cd_methods: method_def list;
      cd_loc : location }


type program =
    { p_modname : modul;
      p_opened  : modul list;
      p_desc    : program_desc list }

and program_desc =
  | Pclass of class_def
  | Pconst of const_dec
  | Ptype of type_dec

