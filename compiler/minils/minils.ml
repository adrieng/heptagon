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

type type_dec =
    { t_name: name;
      t_desc: tdesc;
      t_loc: location }

and tdesc =
  | Type_abs
  | Type_enum of name list
  | Type_struct of structure

and exp =
    { e_desc: edesc;        (* its descriptor *)
      mutable e_ck: ck;
      mutable e_ty: ty;
      e_loc: location }

and edesc =
  | Econst of const
  | Evar of ident
  | Econstvar of name
  | Efby of const option * exp
  | Etuple of exp list
  | Ecall of op_desc * exp list * ident option (** [op_desc] is the function
                                                   called [exp list] is the
                                                   passed arguments [ident
                                                   option] is the optional reset
                                                   condition *)

  | Ewhen of exp * longname * ident
  | Emerge of ident * (longname * exp) list
  | Eifthenelse of exp * exp * exp
  | Efield of exp * longname
  | Efield_update of longname * exp * exp (*field, record, value*)
  | Estruct of (longname * exp) list
  | Earray of exp list
  | Earray_op of array_op

and array_op =
  | Erepeat of size_exp * exp
  | Eselect of size_exp list * exp (*indices, array*)
  | Eselect_dyn of exp list * exp * exp (* indices, array, default*)
  | Eupdate of size_exp list * exp * exp (*indices, array, value*)
  | Eselect_slice of size_exp * size_exp * exp (*lower bound, upper bound,
                                                 array*)
  | Econcat of exp * exp
  | Eiterator of iterator_type * op_desc * size_exp * exp list * ident option
      (** [op_desc] is the function iterated, [size_exp] is the size of the
          iteration, [exp list] is the passed arguments, [ident option] is the
          optional reset condition *)

and op_desc = { op_name: longname; op_params: size_exp list; op_kind: op_kind }
and op_kind = | Efun | Enode

and ct =
  | Ck of ck
  | Cprod of ct list

and ck =
  | Cbase
  | Cvar of link ref
  | Con of ck * longname * ident

and link =
  | Cindex of int
  | Clink of ck

and const =
  | Cint of int
  | Cfloat of float
  | Cconstr of longname
  | Carray of size_exp * const

and pat =
  | Etuplepat of pat list
  | Evarpat of ident

type eq =
    { eq_lhs : pat;
      eq_rhs : exp;
      eq_loc : location }

type var_dec =
    { v_ident : ident;
      v_type : ty;
      v_clock : ck }

type contract =
    { c_assume : exp;
      c_enforce : exp;
      c_controllables : var_dec list;
      c_local : var_dec list;
      c_eq : eq list;
    }

type node_dec =
    { n_name   : name;
      n_input  : var_dec list;
      n_output : var_dec list;
      n_contract : contract option;
      n_local  : var_dec list;
      n_equs   : eq list;
      n_loc    : location;
      n_params : param list;
      n_params_constraints : size_constraint list;
      n_params_instances : (int list) list; }(*TODO commenter ou passer en env*)

type const_dec =
    { c_name : name;
      c_value : size_exp;
      c_loc : location; }

type program =
    { p_pragmas: (name * string) list;
      p_opened : name list;
      p_types  : type_dec list;
      p_nodes  : node_dec list;
      p_consts : const_dec list; }



(*Helper functions to build the AST*)

let mk_exp ?(exp_ty = Tprod []) ?(clock = Cbase) ?(loc = no_location) desc =
  { e_desc = desc; e_ty = exp_ty; e_ck = clock; e_loc = loc }

let mk_var_dec ?(clock = Cbase) ident ty =
  { v_ident = ident; v_type = ty;
    v_clock = clock }

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

let mk_op ?(op_params = []) ?(op_kind = Enode) lname =
  { op_name = lname; op_params = op_params; op_kind = op_kind }

let void = mk_exp (Etuple [])

