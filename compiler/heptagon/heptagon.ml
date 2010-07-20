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
open Ident
open Static
open Signature
open Types

type state_name = name

type iterator_type =
  | Imap
  | Ifold
  | Imapfold

type exp = { e_desc : desc; e_ty : ty; e_loc : location }

and desc =
  | Econst of static_exp
  | Evar of var_ident
  | Elast of var_ident
  | Epre of static_exp option * exp
  | Efby of exp * exp
  | Estruct of (field_name * exp) list
  | Eapp of app * exp list * exp option
  | Eiterator of iterator_type * app * static_exp * exp list * exp option

and app = { a_op: op; a_params: static_exp list; a_unsafe: bool }

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
  | Eselect_slice
  | Eupdate
  | Econcat

and pat =
  | Etuplepat of pat list
  | Evarpat of var_ident

type eq = { eq_desc : eqdesc; eq_statefull : bool; eq_loc : location }

and eqdesc =
  | Eautomaton of state_handler list
  | Eswitch of exp * switch_handler list
  | Epresent of present_handler list * block
  | Ereset of eq list * exp
  | Eeq of pat * exp

and block = {
  b_local : var_dec list;
  b_equs : eq list;
  b_defnames : ty Env.t;
  b_statefull : bool;
  b_loc : location }

and state_handler = {
  s_state : state_name;
  s_block : block;
  s_until : escape list;
  s_unless : escape list }

and escape = {
  e_cond : exp;
  e_reset : bool;
  e_next_state : state_name }

and switch_handler = { w_name : constructor_name; w_block : block }

and present_handler = { p_cond : exp; p_block : block }

and var_dec = {
  v_ident : var_ident;
  mutable v_type : ty;
  v_last : last;
  v_loc : location }

and last = Var | Last of static_exp option

type type_dec = { t_name : name; t_desc : type_dec_desc; t_loc : location }

and type_dec_desc = Type_abs | Type_enum of name list | Type_struct of structure

type contract = {
  c_assume : exp;
  c_enforce : exp;
  c_block : block }

type node_dec = {
  n_name : name;
  n_statefull : bool;
  n_input : var_dec list;
  n_output : var_dec list;
  n_contract : contract option;
  n_block : block;
  n_loc : location;
  n_params : param list;
  n_params_constraints : size_constraint list }

type const_dec = {
  c_name : name;
  c_type : ty;
  c_value : static_exp;
  c_loc : location }

type program = {
  p_modname : name;
  p_opened : name list;
  p_types : type_dec list;
  p_nodes : node_dec list;
  p_consts : const_dec list }

type signature = {
  sig_name : name;
  sig_inputs : arg list;
  sig_statefull : bool;
  sig_outputs : arg list;
  sig_params : param list }

type interface = interface_decl list

and interface_decl = { interf_desc : interface_desc; interf_loc : location }

and interface_desc =
  | Iopen of name
  | Itypedef of type_dec
  | Iconstdef of const_dec
  | Isignature of signature

(* Helper functions to create AST. *)
let mk_exp desc ty =
  { e_desc = desc; e_ty = ty; e_loc = no_location; }

let mk_op ?(params=[]) ?(unsafe=false) op =
  { a_op = op; a_params = params; a_unsafe = unsafe }

let mk_op_app ?(params=[]) ?(unsafe=false) ?(reset=None) op args =
  Eapp(mk_op ~params:params ~unsafe:unsafe op, args, reset)

let mk_type_dec name desc =
  { t_name = name; t_desc = desc; t_loc = no_location; }

let mk_equation ?(statefull = true) desc =
  { eq_desc = desc; eq_statefull = statefull; eq_loc = no_location; }

let mk_var_dec ?(last = Var) name ty  =
  { v_ident = name; v_type = ty;
    v_last = last; v_loc = no_location }

let mk_block ?(statefull = true) defnames eqs =
  { b_local = []; b_equs = eqs; b_defnames = defnames;
    b_statefull = statefull; b_loc = no_location }

let dfalse =
  mk_exp (Econst (mk_static_exp (Sconstructor Initial.pfalse)))
         (Tid Initial.pbool)
let dtrue =
  mk_exp (Econst (mk_static_exp (Sconstructor Initial.ptrue)))
         (Tid Initial.pbool)

let mk_ifthenelse e1 e2 e3 =
  { e3 with e_desc = mk_op_app Eifthenelse [e1; e2; e3] }

let mk_simple_equation pat e =
  mk_equation ~statefull:false (Eeq(pat, e))

let mk_switch_equation ?(statefull = true) e l =
  mk_equation ~statefull:statefull (Eswitch (e, l))

(** @return a size exp operator from a Heptagon operator. *)
let op_from_app app =
  match app.a_op with
    | Efun op -> op_from_app_name op
    | _ -> raise Not_static

(** Translates a Heptagon exp into a static size exp. *)
(*let rec static_exp_of_exp e =
  match e.e_desc with
    | Econst se -> se
    | _ -> raise Not_static *)

(** @return the set of variables defined in [pat]. *)
let vars_pat pat =
  let rec _vars_pat locals acc = function
    | Evarpat x ->
        if (IdentSet.mem x locals) or (IdentSet.mem x acc)
        then acc
        else IdentSet.add x acc
    | Etuplepat pat_list -> List.fold_left (_vars_pat locals) acc pat_list
  in _vars_pat IdentSet.empty IdentSet.empty pat


