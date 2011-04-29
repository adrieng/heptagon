(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* Generic mapred over Heptagon AST *)

(* The basic idea is to provide a top-down pass over an Heptagon AST. If you
   call [program_it hept_funs_default acc p], with [p] an heptagon program and
   [acc] the accumulator of your choice, it will go through the whole AST,
   passing the accumulator without touching it, and applying the identity
   function on the AST. It'll return [p, acc].

   To customize your pass, you need to redefine some functions of the
   [hept_funs_default] record. Each field in the record handles one node type,
   and the function held in the field will be called when the iterator
   encounters the corresponding node type.

   You can imitate the default functions defined here, and named corresponding
   to the [hep_it_funs] field (corresponding to the Heptagon AST type).  There
   are two types of functions, the ones handling record types, and the more
   special ones handling sum types. If you don't want to deal with every
   constructor, you can simply finish your matching with [| _ -> raise
   Misc.Fallback]: it will then fall back to the generic handling for these
   construtors, defined in this file.

   Note that the iterator is a top-down one. If you want to use it in a
   bottom-up manner (e.g. visiting expressions before visiting an equation), you
   need to manually call the proper recursive function (defined here) in the
   beginning of your handler. For example:

   [
   let eq funs acc eq =
     let (eq, acc) = Hept_mapfold.eq funs acc eq in
     ...
     (eq, acc)
   ]

   The record provided here and the functions to iterate over any type
   ([type_it]) enable lots of different ways to deal with the AST.

   Discover it by yourself !*)

(* /!\ Do not EVER put in your funs record one of the generic iterator function
   [type_it]. You should always put a custom version or the default version
   provided in this file. Trespassers will loop infinitely! /!\ *)

open Misc
open Errors
open Global_mapfold
open Heptagon

type 'a hept_it_funs = {
  app            : 'a hept_it_funs -> 'a -> app -> app * 'a;
  block          : 'a hept_it_funs -> 'a -> block -> block * 'a;
  edesc          : 'a hept_it_funs -> 'a -> desc -> desc * 'a;
  eq             : 'a hept_it_funs -> 'a -> eq -> eq * 'a;
  eqdesc         : 'a hept_it_funs -> 'a -> eqdesc -> eqdesc * 'a;
  escape_unless  : 'a hept_it_funs -> 'a -> escape -> escape * 'a;
  escape_until   : 'a hept_it_funs -> 'a -> escape -> escape * 'a;
  exp            : 'a hept_it_funs -> 'a -> exp -> exp * 'a;
  pat            : 'a hept_it_funs -> 'a -> pat -> pat * 'a;
  present_handler: 'a hept_it_funs -> 'a -> present_handler -> present_handler * 'a;
  state_handler  : 'a hept_it_funs -> 'a -> state_handler -> state_handler * 'a;
  switch_handler : 'a hept_it_funs -> 'a -> switch_handler -> switch_handler * 'a;
  var_dec        : 'a hept_it_funs -> 'a -> var_dec -> var_dec * 'a;
  last           : 'a hept_it_funs -> 'a -> last -> last * 'a;
  contract       : 'a hept_it_funs -> 'a -> contract -> contract * 'a;
  node_dec       : 'a hept_it_funs -> 'a -> node_dec -> node_dec * 'a;
  const_dec      : 'a hept_it_funs -> 'a -> const_dec -> const_dec * 'a;
  program        : 'a hept_it_funs -> 'a -> program -> program * 'a;
  program_desc   : 'a hept_it_funs -> 'a -> program_desc -> program_desc * 'a;
  global_funs    : 'a Global_mapfold.global_it_funs }


let rec exp_it funs acc e = funs.exp funs acc e
and exp funs acc e =
  let e_desc, acc = edesc_it funs acc e.e_desc in
  let e_ty, acc = ty_it funs.global_funs acc e.e_ty in
  { e with e_desc = e_desc; e_ty = e_ty }, acc

and edesc_it funs acc ed =
  try funs.edesc funs acc ed
  with Fallback -> edesc funs acc ed
and edesc funs acc ed = match ed with
  | Econst se ->
      let se, acc = static_exp_it funs.global_funs acc se in
      Econst se, acc
  | Evar _ | Elast _ -> ed, acc
  | Epre (se, e) ->
      let se, acc = optional_wacc (static_exp_it funs.global_funs) acc se in
      let e, acc = exp_it funs acc e in
      Epre (se, e), acc
  | Efby (e1, e2) ->
      let e1, acc = exp_it funs acc e1 in
      let e2, acc = exp_it funs acc e2 in
      Efby (e1,e2), acc
  | Estruct n_e_list ->
      let aux acc (n,e) =
        let e, acc = exp_it funs acc e in
        (n,e), acc in
      let n_e_list, acc = mapfold aux acc n_e_list in
      Estruct n_e_list, acc
  | Eapp (app, args, reset) ->
      let app, acc = app_it funs acc app in
      let args, acc = mapfold (exp_it funs) acc args in
      let reset, acc = optional_wacc (exp_it funs) acc reset in
      Eapp (app, args, reset), acc
  | Eiterator (i, app, param, pargs, args, reset) ->
      let app, acc = app_it funs acc app in
      let param, acc = static_exp_it funs.global_funs acc param in
      let pargs, acc = mapfold (exp_it funs) acc pargs in
      let args, acc = mapfold (exp_it funs) acc args in
      let reset, acc = optional_wacc (exp_it funs) acc reset in
      Eiterator (i, app, param, pargs, args, reset), acc
  | Ewhen (e, c, n) ->
      let e, acc = exp_it funs acc e in
      Ewhen (e, c, n), acc
  | Emerge (n, c_e_list) ->
      let aux acc (c,e) =
        let e, acc = exp_it funs acc e in
        (c,e), acc in
      let c_e_list, acc = mapfold aux acc c_e_list in
      Emerge (n, c_e_list), acc
  | Esplit (e1, e2) ->
      let e1, acc = exp_it funs acc e1 in
      let e2, acc = exp_it funs acc e2 in
        Esplit(e1, e2), acc


and app_it funs acc a = funs.app funs acc a
and app funs acc a =
  let p, acc = mapfold (static_exp_it funs.global_funs) acc a.a_params in
  { a with a_params = p }, acc


and pat_it funs acc p =
  try funs.pat funs acc p
  with Fallback -> pat funs acc p
and pat funs acc p = match p with
  | Etuplepat pl ->
      let pl, acc = mapfold (pat_it funs) acc pl in
      Etuplepat pl, acc
  | Evarpat _ -> p, acc


and eq_it funs acc eq = funs.eq funs acc eq
and eq funs acc eq =
  let eqdesc, acc = eqdesc_it funs acc eq.eq_desc in
  { eq with eq_desc = eqdesc }, acc


and eqdesc_it funs acc eqd =
  try funs.eqdesc funs acc eqd
  with Fallback -> eqdesc funs acc eqd
and eqdesc funs acc eqd = match eqd with
  | Eautomaton st_h_l ->
      let st_h_l, acc = mapfold (state_handler_it funs) acc st_h_l in
      Eautomaton st_h_l, acc
  | Eswitch (e, sw_h_l) ->
      let e, acc = exp_it funs acc e in
      let sw_h_l, acc = mapfold (switch_handler_it funs) acc sw_h_l in
      Eswitch (e, sw_h_l), acc
  | Epresent (p_h_l, b) ->
      let p_h_l, acc = mapfold (present_handler_it funs) acc p_h_l in
      let b, acc = block_it funs acc b in
      Epresent (p_h_l, b), acc
  | Ereset (b, e) ->
      let b, acc = block_it funs acc b in
      let e, acc = exp_it funs acc e in
      Ereset (b, e), acc
  | Eblock b ->
      let b, acc = block_it funs acc b in
      Eblock b, acc
  | Eeq (p, e) ->
      let p, acc = pat_it funs acc p in
      let e, acc = exp_it funs acc e in
      Eeq (p, e), acc


and block_it funs acc b = funs.block funs acc b
and block funs acc b =
  (* TODO defnames ty ?? *)
  let b_local, acc = mapfold (var_dec_it funs) acc b.b_local in
  let b_equs, acc = mapfold (eq_it funs) acc b.b_equs in
  { b with b_local = b_local; b_equs = b_equs }, acc


and state_handler_it funs acc s = funs.state_handler funs acc s
and state_handler funs acc s =
  let s_unless, acc = mapfold (escape_unless_it funs) acc s.s_unless in
  let s_block, acc = block_it funs acc s.s_block in
  let s_until, acc = mapfold (escape_until_it funs) acc s.s_until in
  { s with s_block = s_block; s_until = s_until; s_unless = s_unless }, acc


(** escape is a generic function to deal with the automaton state escapes,
    still the iterator function record differentiate until and unless
    with escape_until_it and escape_unless_it *)
and escape_unless_it funs acc esc = funs.escape_unless funs acc esc
and escape_until_it funs acc esc = funs.escape_until funs acc esc
and escape funs acc esc =
  let e_cond, acc = exp_it funs acc esc.e_cond in
  { esc with e_cond = e_cond }, acc


and switch_handler_it funs acc sw = funs.switch_handler funs acc sw
and switch_handler funs acc sw =
  let w_block, acc = block_it funs acc sw.w_block in
  { sw with w_block = w_block }, acc


and present_handler_it funs acc ph = funs.present_handler funs acc ph
and present_handler funs acc ph =
  let p_cond, acc = exp_it funs acc ph.p_cond in
  let p_block, acc = block_it funs acc ph.p_block in
  { ph with p_cond = p_cond; p_block = p_block }, acc

and var_dec_it funs acc vd = funs.var_dec funs acc vd
and var_dec funs acc vd =
  (* TODO v_type ??? *)
  let v_last, acc = last_it funs acc vd.v_last in
  { vd with v_last = v_last }, acc


and last_it funs acc l =
  try funs.last funs acc l
  with Fallback -> last funs acc l
and last funs acc l = match l with
  | Var -> l, acc
  | Last sto ->
      let sto, acc = optional_wacc (static_exp_it funs.global_funs) acc sto in
      Last sto, acc


and contract_it funs acc c = funs.contract funs acc c
and contract funs acc c =
  let c_assume, acc = exp_it funs acc c.c_assume in
  let c_enforce, acc = exp_it funs acc c.c_enforce in
  let c_block, acc = block_it funs acc c.c_block in
  let c_controllables, acc = mapfold (var_dec_it funs) acc c.c_controllables in
  { c with
    c_assume = c_assume;
    c_enforce = c_enforce;
    c_block = c_block;
    c_controllables = c_controllables },
  acc

and param_it funs acc vd = funs.param funs acc vd
and param funs acc vd =
  let v_last, acc = last_it funs acc vd.v_last in
  { vd with v_last = v_last }, acc

and node_dec_it funs acc nd =
  Idents.enter_node nd.n_name;
  funs.node_dec funs acc nd
and node_dec funs acc nd =
  let n_input, acc = mapfold (var_dec_it funs) acc nd.n_input in
  let n_output, acc = mapfold (var_dec_it funs) acc nd.n_output in
  let n_params, acc = mapfold (param_it funs.global_funs) acc nd.n_params in
  let n_contract, acc =  optional_wacc (contract_it funs) acc nd.n_contract in
  let n_block, acc = block_it funs acc nd.n_block in
  { nd with
      n_input = n_input;
      n_output = n_output;
      n_block = n_block;
      n_params = n_params;
      n_contract = n_contract }
  , acc


and const_dec_it funs acc c = funs.const_dec funs acc c
and const_dec funs acc c =
  let c_type, acc = ty_it funs.global_funs acc c.c_type in
  let c_value, acc = static_exp_it funs.global_funs acc c.c_value in
  { c with c_value = c_value; c_type = c_type }, acc

and program_it funs acc p = funs.program funs acc p
and program funs acc p =
  let p_desc, acc = mapfold (program_desc_it funs) acc p.p_desc in
  { p with p_desc = p_desc }, acc

and program_desc_it funs acc pd =
  try funs.program_desc funs acc pd
  with Fallback -> program_desc funs acc pd
and program_desc funs acc pd = match pd with
  | Pconst cd -> let cd, acc = const_dec_it funs acc cd in Pconst cd, acc
  | Ptype td -> pd, acc
  | Pnode n -> let n, acc = node_dec_it funs acc n in Pnode n, acc

let defaults = {
  app = app;
  block = block;
  edesc = edesc;
  eq = eq;
  eqdesc = eqdesc;
  escape_unless = escape;
  escape_until = escape;
  exp = exp;
  pat = pat;
  present_handler = present_handler;
  state_handler = state_handler;
  switch_handler = switch_handler;
  var_dec = var_dec;
  last = last;
  contract = contract;
  node_dec = node_dec;
  const_dec = const_dec;
  program = program;
  program_desc = program_desc;
  global_funs = Global_mapfold.defaults }



let defaults_stop = {
  app = stop;
  block = stop;
  edesc = stop;
  eq = stop;
  eqdesc = stop;
  escape_unless = stop;
  escape_until = stop;
  exp = stop;
  pat = stop;
  present_handler = stop;
  state_handler = stop;
  switch_handler = stop;
  var_dec = stop;
  last = stop;
  contract = stop;
  node_dec = stop;
  const_dec = stop;
  program = stop;
  program_desc = stop;
  global_funs = Global_mapfold.defaults_stop }





