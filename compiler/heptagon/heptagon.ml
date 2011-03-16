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
  e_ct_annot  : ct;
  e_base_ck   : ck;
  e_loc       : location }

and desc =
  | Econst of static_exp
  | Evar of var_ident
  | Elast of var_ident
  (* the static_exp purpose is the initialization of the mem_var *)
  | Epre of static_exp option * exp
  | Efby of exp * exp
  | Estruct of (field_name * exp) list
  | Ewhen of exp * constructor_name * exp
    (** exp when Constructor(ident) *)
  | Emerge of exp * (constructor_name * exp) list
    (** merge ident (Constructor -> exp)+ *)
  | Eapp of app * exp list * exp option
  | Eiterator of iterator_type * app * static_exp
                  * exp list * exp list * exp option

and app = {
  a_op     : op;
  a_params : static_exp list;
  a_unsafe : bool;
  a_inlined : bool }

and op =
  | Eequal
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
  b_defnames  : ty Env.t;
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
  n_name      : qualname;
  n_stateful : bool;
  n_input     : var_dec list;
  n_output    : var_dec list;
  n_contract  : contract option;
  n_block     : block;
  n_loc       : location;
  n_params    : param list;
  n_params_constraints : size_constraint list }

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
  sig_name      : qualname;
  sig_inputs    : arg list;
  sig_stateful : bool;
  sig_outputs   : arg list;
  sig_params    : param list;
  sig_loc       : location }

type interface = interface_decl list

and interface_decl = {
  interf_desc : interface_desc;
  interf_loc  : location }

and interface_desc =
  | Iopen of modul
  | Itypedef of type_dec
  | Iconstdef of const_dec
  | Isignature of signature

(* Helper functions to create AST. *)
let mk_exp desc ?(ct_annot = Clocks.invalid_clock) ?(loc = no_location) ty  =
  { e_desc = desc; e_ty = ty; e_ct_annot = ct_annot;
    e_base_ck = Cbase; e_loc = loc; }

let mk_app ?(params=[]) ?(unsafe=false) ?(inlined=false) op =
  { a_op = op; a_params = params; a_unsafe = unsafe; a_inlined = inlined }

let mk_op_app ?(params=[]) ?(unsafe=false) ?(reset=None) op args =
  Eapp(mk_app ~params:params ~unsafe:unsafe op, args, reset)

let mk_type_dec name desc =
  { t_name = name; t_desc = desc; t_loc = no_location; }

let mk_equation ?(stateful = true) desc =
  { eq_desc = desc; eq_stateful = stateful; eq_loc = no_location; }

let mk_var_dec ?(last = Var) ?(clock = fresh_clock()) name ty =
  { v_ident = name; v_type = ty; v_clock = clock;
    v_last = last; v_loc = no_location }

let mk_block ?(stateful = true) ?(defnames = Env.empty) ?(locals = []) eqs =
  { b_local = locals; b_equs = eqs; b_defnames = defnames;
    b_stateful = stateful; b_loc = no_location; }

let dfalse =
  mk_exp (Econst (mk_static_bool false)) (Tid Initial.pbool)
let dtrue =
  mk_exp (Econst (mk_static_bool true)) (Tid Initial.pbool)

let mk_ifthenelse e1 e2 e3 =
  { e3 with e_desc = mk_op_app Eifthenelse [e1; e2; e3] }

let mk_simple_equation pat e =
  mk_equation ~stateful:false (Eeq(pat, e))

let mk_switch_equation ?(stateful = true) e l =
  mk_equation ~stateful:stateful (Eswitch (e, l))

let mk_signature name ins outs stateful params loc =
  { sig_name = name;
    sig_inputs = ins;
    sig_stateful = stateful;
    sig_outputs = outs;
    sig_params = params;
    sig_loc = loc }

let mk_node
    ?(input = []) ?(output = []) ?(contract = None) ?(local = [])
    ?(stateful = true) ?(loc = no_location) ?(param = []) ?(constraints = [])
    name block =
  { n_name = name;
    n_stateful = stateful;
    n_input = input;
    n_output = output;
    n_contract = contract;
    n_block = block;
    n_loc = loc;
    n_params = param;
    n_params_constraints = constraints }

(** @return the set of variables defined in [pat]. *)
let vars_pat pat =
  let rec _vars_pat locals acc = function
    | Evarpat x ->
        if (IdentSet.mem x locals) or (IdentSet.mem x acc)
        then acc
        else IdentSet.add x acc
    | Etuplepat pat_list -> List.fold_left (_vars_pat locals) acc pat_list
  in _vars_pat IdentSet.empty IdentSet.empty pat

(** @return whether an object of name [n] belongs to
    a list of [var_dec]. *)
let rec vd_mem n = function
  | [] -> false
  | vd::l -> vd.v_ident = n or (vd_mem n l)
