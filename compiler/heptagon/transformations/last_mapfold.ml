(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* removing accessed to shared variables (last x)      *)
open Heptagon
open Hept_mapfold
open Ident

(* introduce a fresh equation [last_x = pre(x)] for every *)
(* variable declared with a last *)
let last (eq_list, env, v) { v_ident = n; v_type = t; v_last = last } =
  match last with
    | Var -> (eq_list, env, v)
    | Last(default) ->
        let lastn = Ident.fresh ("last" ^ (sourcename n)) in
        let eq = mk_equation (Eeq (Evarpat lastn,
                                   mk_exp (Epre (default,
                                                 mk_exp (Evar n) t)) t)) in
        eq:: eq_list,
        Env.add n lastn env,
        (mk_var_dec lastn t) :: v

let extend_env env v = List.fold_left last ([], env, []) v

let edesc funs env ed = match ed with
  | Elast x ->
      let lx = Env.find x env in Evar lx, env
  | _ -> raise Misc.Fallback

let block funs env b =
  let eq_lastn_n_list, env, last_v = extend_env env b.b_local in
  let b, _ = Hept_mapfold.block funs env b in
    { b with b_local = b.b_local @ last_v;
        b_equs = eq_lastn_n_list @ b.b_equs }, env

let contract funs env contract =
  let eq_lastn_n_list, env', last_v = extend_env env contract.c_local in
  let contract, _ = Hept_mapfold.contract funs env contract in
    { contract with c_local = contract.c_local @ last_v;
        c_eq = eq_lastn_n_list @ contract.c_eq }, env

let node_dec funs env n =
  let _, env, _ = extend_env Env.empty n.n_input in
  let eq_lasto_list, env, last_o = extend_env env n.n_output in
  let eq_lastn_n_list, env, last_v = extend_env env n.n_local in
  let n, _  = Hept_mapfold.node_dec funs env n in
    { n with n_local = n.n_local @ last_o @ last_v;
        n_equs = eq_lasto_list @ eq_lastn_n_list @ n.n_equs }, env

let program p =
  let funs = { Hept_mapfold.defaults with
                 node_dec = node_dec; block = block;
                 contract = contract; edesc = edesc } in
  let p, _ = Hept_mapfold.program_it funs Env.empty p in
    p