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
open Idents
open Signature
open Static
open Types
open Clocks

(** Warning: Whenever Minils ast is modified,
    minils_format_version should be incremented. *)
let minils_format_version = "1"

type iterator_type =
  | Imap
  | Imapi
  | Ifold
  | Ifoldi
  | Imapfold

type type_dec = {
  t_name: qualname;
  t_desc: tdesc;
  t_loc: location }

and tdesc =
  | Type_abs
  | Type_alias of ty
  | Type_enum of constructor_name list
  | Type_struct of structure

and exp = {
  e_desc      : edesc;
  e_base_ck   : ck;
  mutable e_ck: ck;
  mutable e_ty: ty;
  e_loc       : location }

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
  | Eiterator of iterator_type * app * static_exp * exp list * exp list * var_ident option
                       (** map f <<n>> (exp, exp...) reset ident *)

and app = { a_op: op; a_params: static_exp list; a_unsafe: bool }
    (** Unsafe applications could have side effects
        and be delicate about optimizations, !be careful! *)

and op =
  | Eequal             (** arg1 = arg2 *)
  | Etuple             (** (args) *)
  | Efun of fun_name   (** "Stateless" longname <<a_params>> (args) reset r *)
  | Enode of fun_name  (** "Stateful" longname <<a_params>> (args) reset r *)
  | Eifthenelse        (** if arg1 then arg2 else arg3 *)
  | Efield             (** arg1.a_param1 *)
  | Efield_update      (** { arg1 with a_param1 = arg2 } *)
  | Earray             (** [ args ] *)
  | Earray_fill        (** [arg1^a_param1] *)
  | Eselect            (** arg1[a_params] *)
  | Eselect_slice      (** arg1[a_param1..a_param2] *)
  | Eselect_dyn        (** arg1.[arg3...] default arg2 *)
  | Eupdate            (** [ arg1 with arg3..arg_n = arg2 ] *)
  | Econcat            (** arg1@@arg2 *)


type pat =
  | Etuplepat of pat list
  | Evarpat of var_ident

type eq = {
  eq_lhs : pat;
  eq_rhs : exp;
  eq_loc : location }

type var_dec = {
  v_ident : var_ident;
  v_type : ty;
  v_clock : ck;
  v_loc : location }

type contract = {
  c_assume : exp;
  c_enforce : exp;
  c_controllables : var_dec list;
  c_local : var_dec list;
  c_eq : eq list }

type node_dec = {
  n_name   : qualname;
  n_stateful : bool;
  n_input  : var_dec list;
  n_output : var_dec list;
  n_contract : contract option;
  (* GD: inglorious hack for controller call
  mutable n_controller_call : var_ident list * var_ident list; *)
  n_local  : var_dec list;
  n_equs   : eq list;
  n_loc    : location;
  n_params : param list;
  n_params_constraints : size_constraint list }

type const_dec = {
  c_name : qualname;
  c_type : ty;
  c_value : static_exp;
  c_loc : location }

type program = {
  p_modname : modul;
  p_format_version : string;
  p_opened : modul list;
  p_types  : type_dec list;
  p_nodes  : node_dec list;
  p_consts : const_dec list }

(*Helper functions to build the AST*)

let mk_exp ~ty ?(clock = fresh_clock())
           ?(loc = no_location) ?(base_clock = Cbase) desc =
  { e_desc = desc; e_ty = ty;
    e_base_ck = base_clock; e_ck = clock; e_loc = loc }

let mk_var_dec ?(loc = no_location) ?(clock = fresh_clock()) ident ty =
  { v_ident = ident; v_type = ty; v_clock = clock; v_loc = loc }

let mk_equation ?(loc = no_location) pat exp =
  { eq_lhs = pat; eq_rhs = exp; eq_loc = loc }

let mk_node
    ?(input = []) ?(output = []) ?(contract = None) ?(local = []) ?(eq = [])
    ?(stateful = true) ?(loc = no_location) ?(param = []) ?(constraints = [])
    ?(pinst = ([],[])) name =
  { n_name = name;
    n_stateful = stateful;
    n_input = input;
    n_output = output;
    n_contract = contract;
 (*   n_controller_call = pinst;*)
    n_local = local;
    n_equs = eq;
    n_loc = loc;
    n_params = param;
    n_params_constraints = constraints }

let mk_type_dec type_desc name loc =
  { t_name = name; t_desc = type_desc; t_loc = loc }

let mk_const_dec id ty e loc =
  { c_name = id; c_type = ty; c_value = e; c_loc = loc }

let mk_app ?(params=[]) ?(unsafe=false) op =
  { a_op = op; a_params = params; a_unsafe = unsafe }

(** The modname field has to be set when known, TODO LG : format_version *)
let mk_program o n t c =
  { p_modname = Module ""; p_format_version = "";
    p_opened = o; p_nodes = n; p_types = t; p_consts = c }

let void = mk_exp ~ty:Types.Tunit (Eapp (mk_app Etuple, [], None))
