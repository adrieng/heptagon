(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* the internal representation *)

open Names
open Location
open Signature
open Types

type iterator_type =
  | Imap
  | Ifold
  | Ifoldi
  | Imapfold

type ty =
  | Tprod of ty list
  | Tid of longname
  | Tarray of ty * exp

and exp =
    { e_desc: desc;
      e_loc: location }

and desc =
  | Econst of static_exp
  | Evar of name
  | Elast of name
  | Epre of exp option * exp
  | Efby of exp * exp
  | Estruct of (longname * exp) list
  | Eapp of app * exp list
  | Eiterator of iterator_type * app * exp * exp list

and app = { a_op: op; a_params: exp list; }

and op =
  | Etuple
  | Enode of longname
  | Efun of longname
  | Eifthenelse
  | Earrow
  | Efield
  | Efield_update (* field name args would be [record ; value] *)
  | Earray
  | Earray_fill
  | Eselect
  | Eselect_dyn
  | Eselect_slice
  | Eupdate
  | Econcat

and pat =
  | Etuplepat of pat list
  | Evarpat of name

type eq =
    { eq_desc : eqdesc;
      eq_loc : location }

and eqdesc =
  | Eautomaton of state_handler list
  | Eswitch of exp * switch_handler list
  | Epresent of present_handler list * block
  | Ereset of block * exp
  | Eeq of pat * exp

and block =
    { b_local: var_dec list;
      b_equs: eq list;
      b_loc: location; }

and state_handler =
    { s_state : name;
      s_block : block;
      s_until : escape list;
      s_unless : escape list; }

and escape =
    { e_cond : exp;
      e_reset : bool;
      e_next_state : name; }

and switch_handler =
    { w_name : longname;
      w_block : block; }

and present_handler =
    { p_cond : exp;
      p_block : block; }

and var_dec =
    { v_name : name;
      v_type : ty;
      v_last : last;
      v_loc  : location; }

and last = Var | Last of exp option

type type_dec =
    { t_name : name;
      t_desc : type_desc;
      t_loc  : location }

and type_desc =
  | Type_abs
  | Type_alias of ty
  | Type_enum of name list
  | Type_struct of (name * ty) list

type contract =
    { c_assume : exp;
      c_enforce : exp;
      c_block : block
    }

type node_dec =
    { n_name      : name;
      n_statefull : bool;
      n_input     : var_dec list;
      n_output    : var_dec list;
      n_contract  : contract option;
      n_block     : block;
      n_loc       : location;
      n_params : var_dec list; }

type const_dec =
    { c_name : name;
      c_type : ty;
      c_value : exp;
      c_loc  : location; }

type program =
    { p_modname : name;
      p_pragmas: (name * string) list;
      p_opened : name list;
      p_types  : type_dec list;
      p_nodes  : node_dec list;
      p_consts : const_dec list; }

type arg = { a_type : ty; a_name : name option }

type signature =
    { sig_name    : name;
      sig_inputs  : arg list;
      sig_statefull : bool;
      sig_outputs : arg list;
      sig_params  : var_dec list; }

type interface = interface_decl list

and interface_decl =
    { interf_desc : interface_desc;
      interf_loc  : location }

and interface_desc =
  | Iopen of name
  | Itypedef of type_dec
  | Iconstdef of const_dec
  | Isignature of signature

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

