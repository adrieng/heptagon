 (**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* Generic mapred over Heptagon Ast *)

open Misc
open Heptagon

exception Fall_back

type exp = { e_desc : edesc }

and edesc =
  | Econst of static_exp
  | Evar of var_ident
  | Elast of var_ident
  | Epre of static_exp option * exp
  | Efby of exp * exp
  | Efield of exp * field_name
  | Estruct of (field_name * exp) list
  | Eapp of app * exp list * exp option
  | Eiterator of iterator_type * app * static_exp * exp list * exp option



let exp_it funs acc e =
  let ed, acc = funs.edesc_it funs acc e.edesc in
  { e with e_desc = ed }, acc

let edesc_it_default funs acc ed = match ed with
  | Econst se -> let se, acc = funs.static_exp_it funs acc se in Econst se, acc
  | Evar _ | Elast _ -> ed, acc
  | Epre (None, e) -> let e, acc = funs.exp_it funs acc e in Epre (None, e), acc
  | Epre (Some se, e) ->
      let se, acc = funs.static_exp_it funs acc se in
      let e, acc = funs.exp_it funs acc e in Epre (Some se, e), acc
  | Efby (e1, e2) ->
      let e1, acc = funs.exp_it funs acc e1 in
      let e2, acc = funs.exp_it funs acc e2 in Efby (e1,e2), acc
  | Efby of exp * exp
  | Efield of exp * field_name
  | Estruct of (field_name * exp) list
  | Eapp of app * exp list * exp option
  | Eiterator of iterator_type * app * static_exp * exp list * exp option

let edesc_it funs acc e =
  try funs.edesc_it funs acc e
  with Fall_back -> edesc_it_default funs acc e




(** const_dec : traverse static_exps *)
let const_it funs acc c =
  let se, acc = funs.static_exp_it funs acc c.c_value in
  { c with c_value = se }, acc



and app = { a_op: op; a_params: static_exp list; a_unsafe: bool }

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
  mutable b_defnames : ty Env.t;
  mutable b_statefull : bool;
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


type contract = {
  c_assume : exp;
  c_enforce : exp;
  c_local : var_dec list;
  c_eq : eq list }

type node_dec = {
  n_input : var_dec list;
  n_output : var_dec list;
  n_local : var_dec list;
  n_equs : eq list }






(** const_dec : traverse static_exps *)
let const_it funs acc c =
  let se, acc = funs.static_exp_it funs acc c.c_value in
  { c with c_value = se }, acc

(** program : traverse const_dec chained to node_dec *)
let program_it funs acc p =
  let cd_list, acc = mapfold (funs.const_it funs) acc p.p_consts in
  let nd_list, acc = mapfold (funs.node_it funs) acc p.p_nodes in
  { p with p_consts = cd_list; p_nodes = nd_list }, acc


let hept_mapfolds = { program_it .... }









