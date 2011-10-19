open Idents
open Signature
open Minils
open Mls_mapfold

(**  Adds an extra equation for outputs that are also memories.
     For instance, if o is an output, then:
       o = v fby e
     becomes
       mem_o = v fby e;
       o = mem_o
*)

let memory_vars_vds nd =
  let build env l =
    List.fold_left (fun env vd -> Env.add vd.v_ident vd env) env l
  in
  let env = build Env.empty nd.n_output in
  let env = build env nd.n_local in
  let mem_var_tys = Mls_utils.node_memory_vars nd in
  List.map (fun (x, _) -> Env.find x env) mem_var_tys

let eq _ (outputs, v, eqs) eq = match eq.eq_lhs, eq.eq_rhs.e_desc with
  | Evarpat x, Efby _ ->
      if Mls_utils.vd_mem x outputs then
        let vd = Mls_utils.vd_find x outputs in
        let x_mem = Idents.gen_var "normalize_mem" ("mem_"^(Idents.name x)) in
        let vd_mem = { vd with v_ident = x_mem } in
        let exp_mem_x = mk_extvalue_exp vd.v_clock vd.v_type
          ~clock:vd.v_clock ~linearity:vd.v_linearity (Wvar x_mem) in
        (* mem_o = v fby e *)
        let eq_copy = { eq with eq_lhs = Evarpat x_mem } in
        (* o = mem_o *)
        let eq = { eq with eq_rhs = exp_mem_x } in
        eq, (outputs, vd_mem::v, eq::eq_copy::eqs)
      else (* this memory is not an output *)
        eq, (outputs, v, eq::eqs)
  | _, _ ->
      eq, (outputs, v, eq::eqs)

(* Leave contract unchanged (no output defined in it) *)
let contract funs acc c = c, acc

let node funs acc nd =
  let outputs_mems = nd.n_output @ memory_vars_vds nd in
  let nd, (_, v, eqs) = Mls_mapfold.node_dec funs (outputs_mems, nd.n_local, []) nd in
  (* return updated node *)
  { nd with n_local = v; n_equs = List.rev eqs }, acc

let program p =
  let funs = { Mls_mapfold.defaults with
    eq = eq; node_dec = node; contract = contract } in
  let p, _ = Mls_mapfold.program_it funs ([], [], []) p in
    p
