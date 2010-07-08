(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* The internal MiniLustre representation *)

open Location
open Names
open Ident
open Signature
open Static
open Types

type iterator_type =
  | Imap
  | Ifold
  | Imapfold

type type_dec = {
  t_name: name;
  t_desc: tdesc;
  t_loc: location }

and tdesc =
  | Type_abs
  | Type_enum of name list
  | Type_struct of structure

and exp = {
  e_desc: edesc;
  mutable e_ck: ck;
  mutable e_ty: ty;
  e_loc: location }

and edesc =
  | Econst of static_exp
  | Evar of var_ident
  | Efby of static_exp option * exp
                       (** static_exp fby exp *)
  | Eapp of app * exp list * var_ident option
                       (** app ~args=(exp,exp...) reset ~r=ident *)
  | Ewhen of exp * constructor_name * var_ident
                       (** exp when Constructor(ident) *)
  | Emerge of var_ident * (constructor_name * exp) list
                       (** merge ident (Constructor -> exp)+ *)
  | Estruct of (field_name * exp) list
                       (** { field=exp; ... } *)
  | Eiterator of iterator_type * app * static_exp * exp list * var_ident option
                       (** map f <<n>> (exp,exp...) reset ident *)

and app = { a_op: op; a_params: static_exp list; a_unsafe: bool }
    (** Unsafe applications could have side effects
        and be delicate about optimizations, !be careful! *)

and op =
  | Etuple             (** (args) *)
  | Efun of fun_name   (** "Stateless" longname <<a_params>> (args) reset r *)
  | Enode of fun_name  (** "Stateful" longname <<a_params>> (args) reset r *)
  | Eifthenelse        (** if arg1 then arg2 else arg3 *)
  | Efield             (** arg1.a_param1 *)
  | Efield_update      (** { arg1 with a_param1 = arg2 } *)
  | Earray             (** [ args ] *)
  | Earray_fill        (** [arg1^arg2] *)
  | Eselect            (** arg1[a_params] *)
  | Eselect_slice      (** arg1[a_param1..a_param2] *)
  | Eselect_dyn        (** arg1.[arg3...] default arg2 *)
  | Eupdate            (** [ arg1 with a_params = arg2 ] *)
  | Econcat            (** arg1@@arg2 *)

and ct =
  | Ck of ck
  | Cprod of ct list

and ck =
  | Cbase
  | Cvar of link ref
  | Con of ck * constructor_name * var_ident

and link =
  | Cindex of int
  | Clink of ck

and pat =
  | Etuplepat of pat list
  | Evarpat of var_ident

type eq = {
  eq_lhs : pat;
  eq_rhs : exp;
  eq_loc : location }

type var_dec = {
  v_ident : var_ident;
  v_type : ty;
  v_clock : ck }

type contract = {
  c_assume : exp;
  c_enforce : exp;
  c_local : var_dec list;
  c_eq : eq list }

type node_dec = {
  n_name   : name;
  n_input  : var_dec list;
  n_output : var_dec list;
  n_contract : contract option;
  n_local  : var_dec list;
  n_equs   : eq list;
  n_loc    : location;
  n_params : param list; (** TODO CP mettre des petits commentaires *)
  n_params_constraints : size_constraint list;
  n_params_instances : (static_exp list) list }

type const_dec = {
  c_name : name;
  c_value : static_exp;
  c_loc : location }

type program = {
  p_opened : name list;
  p_types  : type_dec list;
  p_nodes  : node_dec list;
  p_consts : const_dec list }

(*Helper functions to build the AST*)

let mk_exp ?(exp_ty = Tprod []) ?(clock = Cbase) ?(loc = no_location) desc =
  { e_desc = desc; e_ty = exp_ty; e_ck = clock; e_loc = loc }

let mk_var_dec ?(clock = Cbase) ident ty =
  { v_ident = ident; v_type = ty; v_clock = clock }

let mk_equation ?(loc = no_location) pat exp =
  { eq_lhs = pat; eq_rhs = exp; eq_loc = loc }

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
    n_params = param;
    n_params_constraints = constraints;
    n_params_instances = pinst; }

let mk_type_dec ?(type_desc = Type_abs) ?(loc = no_location) name =
  { t_name = name; t_desc = type_desc; t_loc = loc }

let mk_app ?(params=[]) ?(unsafe=false) op =
  { a_op = op; a_params = params; a_unsafe = unsafe }

let void = mk_exp (Eapp (mk_app Etuple, [], None))

