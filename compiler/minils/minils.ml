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
open Linearity
open Clocks

(** Warning: Whenever Minils ast is modified,
    minils_format_version should be incremented. *)
let minils_format_version = "2"

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

and extvalue = {
  w_desc      : extvalue_desc;
  mutable w_ck: ck;
  w_ty        : ty;
  w_linearity : linearity;
  w_loc       : location }

and extvalue_desc =
  | Wconst of static_exp (*no tuple*)
  | Wvar of var_ident
  | Wfield of extvalue * field_name
  | Wwhen of extvalue * constructor_name * var_ident (** extvalue when Constructor(ident) *)
  | Wreinit of extvalue * extvalue

and exp = {
  e_desc            : edesc;
  e_level_ck        : ck; (*when no data dep, execute the exp on this clock (set by [switch] *)
  mutable e_base_ck : ck;
  mutable e_ct      : ct;
  e_ty              : ty;
  e_linearity : linearity;
  e_loc             : location }

and edesc =
  | Eextvalue of extvalue
  | Efby of static_exp option * extvalue
                       (** static_exp fby extvalue *)
  | Eapp of app * extvalue list * var_ident option
                       (** app ~args=(extvalue,extvalue...) reset ~r=ident *)
  | Ewhen of exp * constructor_name * var_ident  (** e when C(c) *)
  | Emerge of var_ident * (constructor_name * extvalue) list
                       (** merge ident (Constructor -> extvalue)+ *)
  | Estruct of (field_name * extvalue) list
                       (** { field=extvalue; ... } *)
  | Eiterator of iterator_type * app * static_exp list
                 * extvalue list * extvalue list * var_ident option
                       (** map f <<n>> <(extvalue)> (extvalue) reset ident *)

and app = { a_op: op;
            a_params: static_exp list;
            a_unsafe: bool;
            a_id: ident option;
            a_async: async_t option;
            a_inlined: bool }
    (** Unsafe applications could have side effects
        and be delicate about optimizations, !be careful! *)

and op =
  | Eequal             (** arg1 = arg2 *)
  | Efun of fun_name   (** "Stateless" longname <<a_params>> (args) reset r *)
  | Enode of fun_name  (** "Stateful" longname <<a_params>> (args) reset r *)
  | Eifthenelse        (** if arg1 then arg2 else arg3 *)
  | Efield_update      (** { arg1 with a_param1 = arg2 } *)
  | Earray             (** [ args ] *)
  | Earray_fill        (** [arg1^a_param1^..^a_paramn] *)
  | Eselect            (** arg1[a_params] *)
  | Eselect_slice      (** arg1[a_param1..a_param2] *)
  | Eselect_dyn        (** arg1.[arg3...] default arg2 *)
  | Eselect_trunc      (** arg1[>arg_2 ...<]*)
  | Eupdate            (** [ arg1 with arg3..arg_n = arg2 ] *)
  | Econcat            (** arg1@@arg2 *)
  | Ebang              (** !arg1 *)

type pat =
  | Etuplepat of pat list
  | Evarpat of var_ident

type eq = {
  eq_lhs    : pat;
  eq_rhs    : exp;
  eq_unsafe : bool;
  eq_loc    : location }

type var_dec = {
  v_ident     : var_ident;
  v_type      : ty;
  v_linearity : linearity;
  v_clock     : ck;
  v_loc       : location }

type contract = {
  c_assume        : extvalue;
  c_enforce       : extvalue;
  c_controllables : var_dec list;
  c_local         : var_dec list;
  c_eq            : eq list }

type node_dec = {
  n_name     : qualname;
  n_stateful : bool;
  n_input    : var_dec list;
  n_output   : var_dec list;
  n_contract : contract option;
  (* GD: inglorious hack for controller call *)
  mutable n_controller_call : string list * string list;
  n_local    : var_dec list;
  n_equs     : eq list;
  n_loc      : location;
  n_params   : param list;
  n_param_constraints : constrnt list;
  n_mem_alloc : (ty * Interference_graph.ivar list) list; }

type const_dec = {
  c_name : qualname;
  c_type : ty;
  c_value : static_exp;
  c_loc : location }

type program = {
  p_modname : modul;
  p_format_version : string;
  p_opened : modul list;
  p_desc  : program_desc list }

and program_desc =
  | Pnode of node_dec
  | Pconst of const_dec
  | Ptype of type_dec

type signature = {
  sig_name              : qualname;
  sig_inputs            : arg list;
  sig_stateful          : bool;
  sig_outputs           : arg list;
  sig_params            : param list;
  sig_param_constraints : constrnt list;
  sig_loc               : location }

type interface =
    { i_modname : modul;
      i_opened : modul list;
      i_desc : interface_desc list }

and interface_desc =
  | Itypedef of type_dec
  | Iconstdef of const_dec
  | Isignature of signature


(*Helper functions to build the AST*)

let mk_extvalue ~ty ~linearity ?(clock = fresh_clock()) ?(loc = no_location) desc =
  { w_desc = desc; w_ty = ty; w_linearity = linearity;
    w_ck = clock; w_loc = loc }

let mk_exp level_ck ty ~linearity ?(ck = Cbase)
    ?(ct = fresh_ct ty) ?(loc = no_location) desc =
  { e_desc = desc; e_ty = ty; e_linearity = linearity;
    e_level_ck = level_ck; e_base_ck = ck; e_ct = ct; e_loc = loc }

let mk_var_dec ?(loc = no_location) ident ty linearity ck =
  { v_ident = ident; v_type = ty; v_linearity = linearity;  v_clock = ck; v_loc = loc }

let mk_extvalue_exp ?(clock = fresh_clock())
    ?(loc = no_location) level_ck ty ~linearity desc =
  mk_exp ~ck:clock ~loc:loc level_ck ty ~linearity:linearity
    (Eextvalue (mk_extvalue ~clock:clock ~loc:loc ~linearity:linearity ~ty:ty desc))

let mk_equation ?(loc = no_location) unsafe pat exp =
  { eq_lhs = pat; eq_rhs = exp; eq_unsafe = unsafe; eq_loc = loc }

let mk_node
    ?(input = []) ?(output = []) ?(contract = None) ?(pinst = ([],[]))
    ?(local = []) ?(eq = [])
    ?(stateful = true) ?(loc = no_location) ?(param = []) ?(constraints = [])
    ?(mem_alloc=[])
    name =
  { n_name = name;
    n_stateful = stateful;
    n_input = input;
    n_output = output;
    n_contract = contract;
    n_controller_call = pinst;
    n_local = local;
    n_equs = eq;
    n_loc = loc;
    n_params = param;
    n_param_constraints = constraints;
    n_mem_alloc = mem_alloc }

let mk_type_dec type_desc name loc =
  { t_name = name; t_desc = type_desc; t_loc = loc }

let mk_const_dec id ty e loc =
  { c_name = id; c_type = ty; c_value = e; c_loc = loc }

let mk_app ?(params=[]) ?(async=None) ?(unsafe=false) ?(id=None) ?(inlined=false) op =
  { a_op = op; a_params = params; a_unsafe = unsafe;
    a_async = async;
    a_id = id; a_inlined = inlined }

