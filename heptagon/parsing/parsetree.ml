(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* the internal representation *)
(* $Id$ *)

open Location
open Names
open Linearity
open Misc

type inlining_policy =
  | Ino
  | Ione
  | Irec

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
    { a_op : op; (* change of global name after typing *)
      a_inlined : inlining_policy; (* node to inline or not *)
    }

and op =
  | Epre of const option
  | Efby | Earrow | Eifthenelse | Enode of longname * exp list
  | Eevery of longname * exp list | Eop of longname * exp list
  | Erepeat | Eselect of exp list | Eselect_dyn
  | Eupdate of exp list
  | Eselect_slice
  | Econcat | Ecopy
  | Eiterator of iterator_name * longname * exp list
  | Efield_update of longname
  | Eflatten of longname | Emake of longname

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
      v_linearity : linearity;
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

type signature =
    { sig_name    : name;
      sig_inputs  : (name option * (ty * linearity)) list;
      sig_outputs : (name option * (ty * linearity)) list;
      sig_node    : bool;
      sig_safe    : bool;
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
let emake desc =
  { e_desc = desc; e_loc = get_current_location () }
let e_true () =
  emake (Econst(Cconstr(Modname{ qual="Pervasives"; id="true"})))
let eop op = { a_op = op; a_inlined = Ino }
let eop_inlined op = { a_op = op; a_inlined = Ione }
let tmake name desc =
  { t_name = name; t_desc = desc; t_loc = get_current_location () }
let eqmake desc =
  { eq_desc = desc; eq_loc = get_current_location () }
let imake desc =
  { interf_desc = desc; interf_loc = get_current_location () }
let vmake name (ty, linearity) last =
  { v_name = name; v_type = ty; v_linearity = linearity;
    v_last = last; v_loc = get_current_location () }

let bmake locals eqs =
  { b_local = locals; b_equs = eqs; 
    b_loc = get_current_location () }

let cmake id (ty,_) e =
  { c_name = id; c_type = ty; c_value = e;
    c_loc = get_current_location (); }
