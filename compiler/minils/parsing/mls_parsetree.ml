(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)


open Names
open Location
open Signature
open Types
open Minils


type exp =
    { e_desc: desc;
      e_loc: location }

and desc =
  | Econst of static_exp
  | Evar of name
  | Efby of static_exp option * exp
  | Eapp of app * exp list * name option
  | Ewhen of exp * constructor_name * name
  | Emerge of name * (constructor_name * exp) list
  | Estruct of (field_name * exp) list
  | Eiterator of iterator_type * app * static_exp * exp list * name option


and pat =
  | Etuplepat of pat list
  | Evarpat of name

type eq = {
  eq_lhs : pat;
  eq_rhs : exp;
  eq_loc : location }

and var_dec = {
  v_name : name;
  v_type : ty;
  v_clock : ck;
  v_loc  : location; }


type contract = {
  c_assume : exp;
  c_enforce : exp;
  c_eq : eq list }

type node_dec = {
  n_name      : name;
  n_statefull : bool;
  n_input     : var_dec list;
  n_output    : var_dec list;
  n_contract  : contract option;
  n_local     : var_dec list;
  n_equs      : eq list;
  n_loc       : location;
  n_params    : param list; }

type program = {
  p_modname : name;
  p_format_version : string;
  p_opened : name list;
  p_types  : type_dec list;
  p_nodes  : node_dec list;
  p_consts : const_dec list }


(* Helper functions to create AST. *)
let mk_exp desc loc =
  { e_desc = desc; e_loc = loc }

let mk_app op params =
  { a_op = op; a_params = params }

let mk_call ?(params=[]) op exps =
  Eapp (mk_app op params, exps)

let mk_op_call ?(params=[]) s exps =
  mk_call ~params:params
    (Efun (Modname { qual = "Pervasives"; id = s })) exps

let mk_iterator_call it ln params n exps =
  Eiterator (it, mk_app (Enode ln) params, n, exps)

let mk_constructor_exp f loc =
  mk_exp (Econst (mk_static_exp (Sconstructor f))) loc

let mk_type_dec name desc loc =
  { t_name = name; t_desc = desc; t_loc = loc }

let mk_equation desc loc =
  { eq_desc = desc; eq_loc = loc }

let mk_interface_decl desc loc =
  { interf_desc = desc; interf_loc = loc }

let mk_var_dec name ty last loc =
  { v_name = name; v_type = ty;
    v_last = last; v_loc = loc }

let mk_block locals eqs loc =
  { b_local = locals; b_equs = eqs;
    b_loc = loc }

let mk_const_dec id ty e loc =
  { c_name = id; c_type = ty; c_value = e;
    c_loc = loc }

let mk_arg name ty =
  { a_type = ty; a_name = name }

