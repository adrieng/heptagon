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

type iterator_type =
  | Imap
  | Ifold
  | Imapfold

type ty =
  | Tprod of ty list
  | Tid of longname
  | Tarray of ty * exp

and exp =
    { e_desc: desc;
      e_loc: location }

and desc =
  | Econst of const
  | Evar of name
  | Elast of name
  | Etuple of exp list
  | Eapp of app * exp list
  | Efield of exp * longname
  | Estruct of (longname * exp) list
  | Earray of exp list

and app =
    { a_op : op; }

and op =
  | Epre of const option
  | Efby | Earrow | Eifthenelse
  | Earray_op of array_op
  | Efield_update of longname
  | Ecall of op_desc

and array_op =
  | Erepeat | Eselect of exp list | Eselect_dyn
  | Eupdate of exp list
  | Eselect_slice
  | Econcat
  | Eiterator of iterator_type * op_desc

and op_desc = { op_name : longname; op_params: exp list; op_kind: op_kind }
and op_kind = | Eop | Enode

and const =
  | Cint of int
  | Cfloat of float
  | Cconstr of longname

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
  | Ereset of eq list * exp
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

and last = Var | Last of const option

type type_dec =
    { t_name : name;
      t_desc : type_desc;
      t_loc  : location }

and type_desc =
  | Type_abs
  | Type_enum of name list
  | Type_struct of (name * ty) list

type contract =
    { c_assume : exp;
      c_enforce : exp;
      c_controllables : var_dec list;
      c_local : var_dec list;
      c_eq : eq list;
    }

type node_dec =
    { n_name      : name;
      n_statefull : bool;
      n_input     : var_dec list;
      n_output    : var_dec list;
      n_local     : var_dec list;
      n_contract  : contract option;
      n_equs      : eq list;
      n_loc       : location;
      n_params : name list; }

type const_dec =
    { c_name : name;
      c_type : ty;
      c_value : exp;
      c_loc  : location; }

type program =
    { p_pragmas: (name * string) list;
      p_opened : name list;
      p_types  : type_dec list;
      p_nodes  : node_dec list;
      p_consts : const_dec list; }

type arg = { a_type : ty; a_name : name option }

type signature =
    { sig_name    : name;
      sig_inputs  : arg list;
      sig_outputs : arg list;
      sig_params  : name list; }

type interface = interface_decl list

and interface_decl =
    { interf_desc : interface_desc;
      interf_loc  : location }

and interface_desc =
  | Iopen of name
  | Itypedef of type_dec
  | Isignature of signature

(* Helper functions to create AST. *)
let mk_exp desc =
  { e_desc = desc; e_loc = Location.current_loc () }

let mk_app op =
  { a_op = op; }

let mk_op_desc ln params kind =
  { op_name = ln; op_params = params; op_kind = kind }

let mk_call desc exps =
  Eapp (mk_app (Ecall desc), exps)

let mk_op_call s params exps =
  mk_call (mk_op_desc (Name s) params Eop)  exps

let mk_array_op_call op exps =
  Eapp (mk_app (Earray_op op), exps)

let mk_iterator_call it ln params exps =
  mk_array_op_call (Eiterator (it, mk_op_desc ln params Enode)) exps

let mk_type_dec name desc =
  { t_name = name; t_desc = desc; t_loc = Location.current_loc () }

let mk_equation desc =
  { eq_desc = desc; eq_loc = Location.current_loc () }

let mk_interface_decl desc =
  { interf_desc = desc; interf_loc = Location.current_loc () }

let mk_var_dec name ty last =
  { v_name = name; v_type = ty;
    v_last = last; v_loc = Location.current_loc () }

let mk_block locals eqs =
  { b_local = locals; b_equs = eqs;
    b_loc = Location.current_loc () }

let mk_const_dec id ty e =
  { c_name = id; c_type = ty; c_value = e;
    c_loc = Location.current_loc (); }

let mk_arg name ty =
  { a_type = ty; a_name = name }

