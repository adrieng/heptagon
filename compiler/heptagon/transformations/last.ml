(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* removing accessed to shared variables (last x)      *)

open Misc
open Heptagon
open Ident

(* introduce a fresh equation [last_x = pre(x)] for every *)
(* variable declared with a last *)
let last (eq_list, env, v) { v_ident = n; v_type = t; v_last = last } =
  match last with
    | Var -> (eq_list, env, v)
    | Last(default) ->
        let lastn = Ident.fresh ("last" ^ (sourcename n)) in
        let eq = mk_equation (Eeq (Evarpat lastn,
                                   mk_exp (Eapp (mk_op (Epre default),
                                                 [mk_exp (Evar n) t])) t)) in
        eq:: eq_list,
        Env.add n lastn env,
        (mk_var_dec lastn t) :: v

let extend_env env v = List.fold_left last ([], env, []) v

let rec translate_eq env eq =
  match eq.eq_desc with
    | Ereset(eq_list, e) ->
        { eq with eq_desc = Ereset(translate_eqs env eq_list, translate env e) }
    | Eeq(pat, e) ->
        { eq with eq_desc = Eeq(pat, translate env e) }
    | Eswitch(e, handler_list) ->
        let handler_list =
          List.map (fun ({ w_block = b } as handler) ->
                      { handler with w_block = translate_block env b })
            handler_list in
        { eq with eq_desc = Eswitch(translate env e, handler_list) }
    | Epresent _ | Eautomaton _ -> assert false

and translate_eqs env eq_list = List.map (translate_eq env) eq_list

and translate_block env ({ b_local = v; b_equs = eq_list } as b) =
  let eq_lastn_n_list, env, last_v = extend_env env v in
  let eq_list = translate_eqs env eq_list in
  { b with b_local = v @ last_v; b_equs = eq_lastn_n_list @ eq_list }

and translate env e =
  match e.e_desc with
      Econst _ | Evar _ | Econstvar _ -> e
    | Elast(x) ->
        let lx = Env.find x env in { e with e_desc = Evar(lx) }
    | Etuple(e_list) ->
        { e with e_desc = Etuple(List.map (translate env) e_list) }
    | Eapp(op, e_list) ->
        { e with e_desc = Eapp(op, List.map (translate env) e_list) }
    | Efield(e', field) ->
        { e with e_desc = Efield(translate env e', field) }
    | Estruct(e_f_list) ->
        { e with e_desc =
            Estruct(List.map (fun (f, e) -> (f, translate env e)) e_f_list) }
    | Earray(e_list) ->
        { e with e_desc = Earray(List.map (translate env) e_list) }

let translate_contract env contract =
  match contract with
    | None -> None, env
    | Some { c_local = v;
             c_eq = eq_list;
             c_assume = e_a;
             c_enforce = e_g;
             c_controllables = cl } ->
        let _, env, _ = extend_env env cl in
        let eq_lastn_n_list, env', last_v = extend_env env v in
        let eq_list = translate_eqs env' eq_list in
        let e_a = translate env' e_a in
        let e_g = translate env' e_g in
        Some { c_local = v @ last_v;
               c_eq = eq_lastn_n_list @ eq_list;
               c_assume = e_a;
               c_enforce = e_g;
               c_controllables = List.rev cl },
        env

let node ({ n_input = i; n_local = v; n_output = o;
            n_equs = eq_list; n_contract  = contract } as n) =
  let _, env, _ = extend_env Env.empty i in
  let eq_lasto_list, env, last_o = extend_env env o in
  let contract, env = translate_contract env contract in
  let eq_lastn_n_list, env, last_v = extend_env env v in
  let eq_list = translate_eqs env eq_list in
  { n with
      n_input = i;
      n_output = o;
      n_local = v @ last_o @ last_v;
      n_contract = contract;
      n_equs = eq_lasto_list @ eq_lastn_n_list @ eq_list }

let program ({ p_types = pt_list; p_nodes = n_list } as p) =
  { p with p_types = pt_list; p_nodes = List.map node n_list }
