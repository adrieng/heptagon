(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* the internal representation *)
open Location
open Misc
open Names
open Idents
open Static
open Signature
open Types
open Linearity
open Clocks
open Initial

type state_name = name

type iterator_type =
  | Imap
  | Imapi
  | Ifold
  | Ifoldi
  | Imapfold

type exp = {
  e_desc      : desc;
  e_ty        : ty;
  mutable e_ct_annot  : ct option; (* exists when a source annotation exists *)
  e_level_ck  : ck; (* set by the switch pass, represents the activation base of the expression *)
  mutable e_linearity : linearity;
  e_loc       : location }

and desc =
  | Econst of static_exp
  | Evar of var_ident
  | Elast of var_ident
  (* the static_exp purpose is the initialization of the mem_var *)
  | Epre of static_exp option * exp
  | Efby of exp * exp
  | Estruct of (field_name * exp) list
  | Ewhen of exp * constructor_name * var_ident
    (** exp when Constructor(ident) *)
  | Emerge of var_ident * (constructor_name * exp) list
    (** merge ident (Constructor -> exp)+ *)
  | Esplit of exp * exp
  | Eapp of app * exp list * exp option
  | Eiterator of iterator_type * app * static_exp list
                  * exp list * exp list * exp option

and app = {
  a_op     : op;
  a_params : static_exp list;
  a_unsafe : bool;
  a_inlined : bool }

and op =
  | Etuple
  | Efun of fun_name
  | Enode of fun_name
  | Eifthenelse
  | Earrow
  | Efield
  | Efield_update (* field name args would be [record ; value] *)
  | Earray
  | Earray_fill
  | Eselect
  | Eselect_dyn
  | Eselect_trunc
  | Eselect_slice
  | Eupdate
  | Econcat

and pat =
  | Etuplepat of pat list
  | Evarpat of var_ident

type eq = {
  eq_desc      : eqdesc;
  eq_stateful : bool;
  eq_inits    : init;
  eq_loc       : location; }

and eqdesc =
  | Eautomaton of state_handler list
  | Eswitch of exp * switch_handler list
  | Epresent of present_handler list * block
  | Ereset of block * exp
  | Eblock of block
  | Eeq of pat * exp

and block = {
  b_local     : var_dec list;
  b_equs      : eq list;
  b_defnames  : var_dec Env.t;
  b_stateful : bool;
  b_loc       : location; }

and state_handler = {
  s_state  : state_name;
  s_block  : block;
  s_until  : escape list;
  s_unless : escape list }

and escape = {
  e_cond       : exp;
  e_reset      : bool;
  e_next_state : state_name }

and switch_handler = {
  w_name  : constructor_name;
  w_block : block }

and present_handler = {
  p_cond  : exp;
  p_block : block }

and var_dec = {
  v_ident : var_ident;
  v_type  : ty;
  v_linearity : linearity;
  v_clock : ck;
  v_last  : last;
  v_loc   : location }

and last = Var | Last of static_exp option

type type_dec = {
  t_name : qualname;
  t_desc : type_dec_desc;
  t_loc  : location }

and type_dec_desc =
  | Type_abs
  | Type_alias of ty
  | Type_enum of constructor_name list
  | Type_struct of structure

type contract = {
  c_assume  : exp;
  c_enforce : exp;
  c_controllables : var_dec list;
  c_block   : block }

type node_dec = {
  n_name               : qualname;
  n_stateful           : bool;
  n_input              : var_dec list;
  n_output             : var_dec list;
  n_contract           : contract option;
  n_block              : block;
  n_loc                : location;
  n_params             : param list;
  n_param_constraints  : constrnt list }

type const_dec = {
  c_name  : qualname;
  c_type  : ty;
  c_value : static_exp;
  c_loc   : location }

type program = {
  p_modname : modul;
  p_opened  : modul list;
  p_desc    : program_desc list }

and program_desc =
  | Ptype of type_dec
  | Pnode of node_dec
  | Pconst of const_dec


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

