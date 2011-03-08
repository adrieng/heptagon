(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* Object code internal representation *)

(** { 3 Semantics }
  Any variable is a reference to a constant memory.
    Thus [p = e] is not the change of the reference,
    but a recursive copy of what is referenced (deep copy).
    As an example, [x = 3] but also [x = \[3; 4; 5\]]
    and [t1 = t2] with the content of the array [t2] copied into the array [t1].
  Obc is also "SSA" in the sens that a variable is assigned a value only once per call of [step] etc.
    Thus arguments are passed as constant references to a constant memory.

  One exception to the SSA rule is through the [mutable] variables.
    Theses variables can be assigned multiple times.
    Thus a [mutable] argument is passed as a reference to a constant memory.
*)


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
  | Epattern of pattern
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
  | Afor of var_dec * static_exp * static_exp * block
  | Ablock of block

and block =
    { b_locals : var_dec list;
      b_body : act list }

and var_dec =
    { v_ident : var_ident;
      v_type : ty;
      v_loc : location }

type obj_dec =
    { o_ident : obj_ident;
      o_async : async_t option;
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
    { p_modname : modul;
      p_opened : modul list;
      p_types : type_dec list;
      p_consts : const_dec list;
      p_defs  : class_def list }

