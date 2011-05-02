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

let fix_vd_ad env vd ad =
  if Env.mem vd.v_ident env then
    let x_copy = Env.find vd.v_ident env in
      { vd with v_ident = x_copy }, { ad with a_name = Some (Idents.name x_copy) }
  else
    vd, ad

let eq _ (outputs, eqs, env) eq = match eq.eq_lhs, eq.eq_rhs.e_desc with
  | Evarpat x, Efby _ ->
      if Mls_utils.vd_mem x outputs then
        let ty = eq.eq_rhs.e_ty in
        let x_copy = Idents.gen_var "normalize_mem" ("out_"^(Idents.name x)) in
        let exp_x = mk_exp ty (Eextvalue (mk_extvalue ~ty:ty (Wvar x))) in
        let eq_copy = { eq with eq_lhs = Evarpat x_copy; eq_rhs = exp_x } in
        let env = Env.add x x_copy env in
          eq, (outputs, eq::eq_copy::eqs, env)
      else (* this memory is not an output *)
        eq, (outputs, eq::eqs, env)
  | _, _ ->
      eq, (outputs, eq::eqs, env)

let node funs acc nd =
  let nd, (_, eqs, env) = Mls_mapfold.node_dec funs (nd.n_output, [], Env.empty) nd in
  let v = Env.fold
    (fun x _ acc -> (Mls_utils.vd_find x nd.n_output)::acc) env nd.n_local in
  (* update the signature of the node *)
  let f = Modules.find_value nd.n_name in
  let o, sig_o = List.split (List.map2 (fix_vd_ad env) nd.n_output f.node_outputs) in
  let f = { f with node_outputs = sig_o } in
  Modules.replace_value nd.n_name f;
  (* return updated node *)
  { nd with n_local = v; n_equs = List.rev eqs; n_output = o }, acc

let program p =
  let funs = { Mls_mapfold.defaults with eq = eq; node_dec = node } in
  let p, _ = Mls_mapfold.program_it funs ([], [], Env.empty) p in
    p
