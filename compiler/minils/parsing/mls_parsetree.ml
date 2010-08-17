(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Location
open Names
open Signature
open Static
open Types
open Clocks


type exp = {
  e_desc: edesc;
  e_loc: location }

and app = { a_op: Minils.op; a_params: exp list }

and edesc =
  | Econst of static_exp
  | Evar of name
  | Efby of exp option * exp
  | Eapp of Minils.app * exp list * name option
  | Ewhen of exp * constructor_name * name
  | Emerge of name * (constructor_name * exp) list
  | Estruct of (field_name * exp) list
  | Eiterator of
      Minils.iterator_type * app * exp * exp list * name option

and pat =
  | Etuplepat of pat list
  | Evarpat of name

and eq = {
  eq_lhs : pat;
  eq_rhs : exp;
  eq_loc : location }

and var_dec = {
  v_ident : name;
  v_type : ty;
  v_clock : ck;
  v_loc : location }

type node_dec = {
  n_name   : name;
  n_input  : var_dec list;
  n_output : var_dec list;
  n_contract : Minils.contract option;
  n_local  : var_dec list;
  n_equs   : eq list;
  n_loc    : location;
  n_params : param list }

type program = {
  p_modname : name;
  p_format_version : string;
  p_opened : name list;
  p_types  : Minils.type_dec list;
  p_nodes  : node_dec list;
  p_consts : Minils.const_dec list }


(** {Helper functions to build the Parsetree *)

let mk_node
    ?(input = []) ?(output = []) ?(contract = None) ?(local = []) ?(eq = [])
    ?(loc = no_location) ?(param = []) ?(constraints = []) ?(pinst = []) name =
  { n_name = name;
    n_input = input;
    n_output = output;
    n_contract = contract;
    n_local = local;
    n_equs = eq;
    n_loc = loc;
    n_params = param }

(** The modname field has to be set when known, TODO LG : format_version *)
let mk_program o n t c =
  { p_modname = ""; p_format_version = "";
    p_opened = o; p_nodes = n; p_types = t; p_consts = c }

let mk_exp desc loc = { e_desc = desc; e_loc = loc }

let mk_app params op = { a_op = op; a_params = params }

let void = mk_exp (Eapp (Minils.mk_app Minils.Etuple, [], None))

let mk_call ?(unsafe=false) ?(params=[]) reset op exps =
  Eapp (Minils.mk_app ~unsafe:unsafe op ~params:params, exps, reset)

let mk_op_call ?(params=[]) s exps =
  mk_call ~params:params None
          (Minils.Efun (Modname { qual = "Pervasives"; id = s })) exps

let mk_iterator_call it ln params reset n exps =
  Eiterator (it, mk_app params (Minils.Enode ln), n, exps, reset)

let mk_constructor_exp f loc =
  mk_exp (Econst (mk_static_exp (Sconstructor f))) loc

let mk_equation lhs rhs loc =
  { eq_lhs = lhs; eq_rhs = rhs; eq_loc = loc }

let mk_var_dec name ty clock loc =
  { v_ident = name; v_type = ty; v_clock = clock; v_loc = loc }


