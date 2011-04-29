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
open Heptagon

(* Helper functions to create AST. *)
let mk_exp desc ?(ct_annot = Clocks.invalid_clock) ?(loc = no_location) ty  =
  { e_desc = desc; e_ty = ty; e_ct_annot = ct_annot;
    e_base_ck = Cbase; e_loc = loc; }

let mk_app ?(params=[]) ?(unsafe=false) op =
  { a_op = op; a_params = params; a_unsafe = unsafe }

let mk_op_app ?(params=[]) ?(unsafe=false) ?(reset=None) op args =
  Eapp(mk_app ~params:params ~unsafe:unsafe op, args, reset)

let mk_type_dec name desc =
  { t_name = name; t_desc = desc; t_loc = no_location; }

let mk_equation ?(loc=no_location) desc =
  let _, s = Stateful.eqdesc Stateful.funs false desc in
  { eq_desc = desc;
    eq_stateful = s;
    eq_loc = loc; }

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
  mk_equation (Eeq(pat, e))

let mk_switch_equation e l =
  mk_equation (Eswitch (e, l))

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
