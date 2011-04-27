open Minils
open Mls_mapfold

(**  Adds an extra equation for outputs that are also memories.
     For instance, if o is an output, then:
       o = v fby e
     becomes
       mem_o = v fby e;
       o = mem_o
*)

let rec vd_replace vd by_vd vd_l = match vd_l with
  | [] -> []
  | h::t -> if h.v_ident = vd.v_ident then by_vd::t else h::(vd_replace vd by_vd t)

let eq _ (locals, eqs, outs) eq = match eq.eq_lhs, eq.eq_rhs.e_desc with
  | Evarpat x, Efby _ ->
      (try
        let vd_out = Mls_utils.vd_find x outs in (* this memory is also an output *)
        let ty = eq.eq_rhs.e_ty in
        let x_copy = Idents.gen_var "normalize_mem" ("out_"^(Idents.name x)) in
        let vd_x_copy = mk_var_dec ~clock:eq.eq_rhs.e_ck x_copy ty in
        let exp_x = mk_exp ty (Eextvalue (mk_extvalue ~ty:ty (Wvar x))) in
        let eq_copy = { eq with eq_lhs = Evarpat x_copy; eq_rhs = exp_x } in
        eq, (vd_out::locals, eq::eq_copy::eqs, vd_replace vd_out vd_x_copy outs)
      with Not_found -> (* this memory is not an output *)
        eq, (locals, eq::eqs, outs))
  | _, _ ->
      eq, (locals, eq::eqs, outs)

let node funs acc nd =
  let nd, (v, eqs, o) = Mls_mapfold.node_dec funs (nd.n_local, [], nd.n_output) nd in
  (* update the signature of the node *)
  let f = Modules.find_value nd.n_name in
  let f = { f with Signature.node_outputs = Mls_utils.args_of_var_decs o } in
  Modules.replace_value nd.n_name f;
  (* return updated node *)
  { nd with n_local = v; n_equs = List.rev eqs; n_output = o }, acc

let program p =
  let funs = { Mls_mapfold.defaults with eq = eq; node_dec = node } in
  let p, _ = Mls_mapfold.program_it funs ([], [], []) p in
    p
