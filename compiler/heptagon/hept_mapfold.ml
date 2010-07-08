 (**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* Generic mapred over Heptagon Ast *)


(* /!\ do never, never put in your funs record one
  of the generic iterator function (_omega),
  either yours either the _default version *)


open Misc
open Types
open Heptagon


type 'a hept_it_funs = {
  app: 'a hept_it_funs -> 'a -> Heptagon.app -> Heptagon.app * 'a;
  block: 'a hept_it_funs -> 'a -> Heptagon.block -> Heptagon.block * 'a;
  edesc: 'a hept_it_funs -> 'a -> Heptagon.desc -> Heptagon.desc * 'a;
  eq: 'a hept_it_funs -> 'a -> Heptagon.eq -> Heptagon.eq * 'a;
  eqdesc: 'a hept_it_funs -> 'a -> Heptagon.eqdesc -> Heptagon.eqdesc * 'a;
  escape_unless :
    'a hept_it_funs -> 'a -> Heptagon.escape -> Heptagon.escape * 'a;
  escape_until:
    'a hept_it_funs -> 'a -> Heptagon.escape -> Heptagon.escape * 'a;
  exp: 'a hept_it_funs -> 'a -> Heptagon.exp -> Heptagon.exp * 'a;
  pat: 'a hept_it_funs -> 'a -> pat -> Heptagon.pat * 'a;
  present_handler:
    'a hept_it_funs -> 'a -> Heptagon.present_handler
                          -> Heptagon.present_handler * 'a;
  state_handler:
    'a hept_it_funs -> 'a -> Heptagon.state_handler
                          -> Heptagon.state_handler * 'a;
  switch_handler:
    'a hept_it_funs -> 'a -> Heptagon.switch_handler
                          -> Heptagon.switch_handler * 'a;
  var_dec: 'a hept_it_funs -> 'a -> Heptagon.var_dec -> Heptagon.var_dec * 'a;
  last: 'a hept_it_funs -> 'a -> Heptagon.last -> Heptagon.last * 'a;
  contract:
    'a hept_it_funs -> 'a -> Heptagon.contract -> Heptagon.contract * 'a;
  node_dec:
    'a hept_it_funs -> 'a -> Heptagon.node_dec -> Heptagon.node_dec * 'a;
  const_dec:
    'a hept_it_funs -> 'a -> Heptagon.const_dec -> Heptagon.const_dec * 'a;
  program:
    'a hept_it_funs -> 'a -> Heptagon.program -> Heptagon.program * 'a;
  ty_funs: 'a Types.types_it_funs }


let rec exp_it funs acc e = funs.exp funs acc e
and exp funs acc e =
  let ed, acc = edesc_it funs acc e.e_desc in
  { e with e_desc = ed }, acc


and edesc_it funs acc ed =
  try funs.edesc funs acc ed
  with Fallback -> edesc funs acc ed
and edesc funs acc ed = match ed with
  | Econst se ->
      let se, acc = static_exp_it funs.ty_funs acc se in
      Econst se, acc
  | Evar _ | Elast _ -> ed, acc
  | Epre (se, e) ->
      let se, acc = optional_wacc (static_exp_it funs.ty_funs) acc se in
      let e, acc = exp_it funs acc e in
      Epre (se, e), acc
  | Epre (Some se, e) ->
      let se, acc = static_exp_it funs.ty_funs acc se in
      let e, acc = exp_it funs acc e in
      Epre (Some se, e), acc
  | Efby (e1, e2) ->
      let e1, acc = exp_it funs acc e1 in
      let e2, acc = exp_it funs acc e2 in
      Efby (e1,e2), acc
  | Efield (e, n) ->
      let e, acc = exp_it funs acc e in
      Efield(e, n), acc
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
  | Eiterator (i, app, param, args, reset) ->
      let app, acc = app_it funs acc app in
      let param, acc = static_exp_it funs.ty_funs acc param in
      let args, acc = mapfold (exp_it funs) acc args in
      let reset, acc = optional_wacc (exp_it funs) acc reset in
      Eiterator (i, app, param, args, reset), acc


and app_it funs acc a = funs.app funs acc a
and app funs acc a =
  let p, acc = mapfold (static_exp_it funs.ty_funs) acc a.a_params in
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
  | Ereset (eq_l, e) ->
      let eq_l, acc = mapfold (eq_it funs) acc eq_l in
      let e, acc = exp_it funs acc e in
      Ereset (eq_l, e), acc
  | Eeq (p, e) ->
      let p, acc = pat_it funs acc p in
      let e, acc = exp_it funs acc e in
      Eeq (p, e), acc


and block_it funs acc b = funs.block funs acc b
and block funs acc b =
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
  let v_last, acc = last_it funs acc vd.v_last in
  { vd with v_last = v_last }, acc


and last_it funs acc l =
  try funs.last funs acc l
  with Fallback -> last funs acc l
and last funs acc l = match l with
  | Var -> l, acc
  | Last sto ->
      let sto, acc = optional_wacc (static_exp_it funs.ty_funs) acc sto in
      Last sto, acc


and contract_it funs acc c = funs.contract funs acc c
and contract funs acc c =
  let c_assume, acc = exp_it funs acc c.c_assume in
  let c_enforce, acc = exp_it funs acc c.c_enforce in
  let c_local, acc = mapfold (var_dec_it funs) acc c.c_local in
  let c_eq, acc = mapfold (eq_it funs) acc c.c_eq in
  { c with
    c_assume = c_assume; c_enforce = c_enforce; c_local = c_local; c_eq = c_eq }
  , acc


and node_dec_it funs acc nd = funs.node_dec funs acc nd
and node_dec funs acc nd =
  let n_input, acc = mapfold (var_dec_it funs) acc nd.n_input in
  let n_output, acc = mapfold (var_dec_it funs) acc nd.n_output in
  let n_local, acc = mapfold (var_dec_it funs) acc nd.n_local in
  let n_equs, acc = mapfold (eq_it funs) acc nd.n_equs in
  { nd with
    n_input = n_input; n_output = n_output; n_local = n_local; n_equs = n_equs }
  , acc



and const_dec_it funs acc c = funs.const_dec funs acc c
and const_dec funs acc c =
  let se, acc = static_exp_it funs.ty_funs acc c.c_value in
  { c with c_value = se }, acc

and program_it funs acc p = funs.program funs acc p
and program funs acc p =
  let cd_list, acc = mapfold (const_dec_it funs) acc p.p_consts in
  let nd_list, acc = mapfold (node_dec_it funs) acc p.p_nodes in
  { p with p_consts = cd_list; p_nodes = nd_list }, acc

let hept_funs_default = {
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
  ty_funs = Types.types_funs_default }







