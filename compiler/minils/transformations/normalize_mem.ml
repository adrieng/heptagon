open Minils
open Mls_mapfold

(**  Adds an extra equation for outputs that are also memories.
     For instance, if o is an output, then:
       o = v fby e
     becomes
       mem_o = v fby e;
       o = mem_o
*)

let eq _ (v, eqs) eq = match eq.eq_lhs, eq.eq_rhs.e_desc with
  | Evarpat x, Efby _ ->
      if not (Mls_utils.vd_mem x v) then (* this memory is also an output *)
        let ty = eq.eq_rhs.e_ty in
        let x_copy = Idents.gen_var "normalize_mem" ("mem_"^(Idents.name x)) in
        let vd = mk_var_dec ~clock:eq.eq_rhs.e_ck x_copy ty in
        let x_copy_exp = mk_exp ty (Eextvalue (mk_extvalue ~ty:ty (Wvar x_copy))) in
        let eq_copy = { eq with eq_rhs = x_copy_exp } in
        let eq = { eq with eq_lhs = Evarpat x_copy } in
          eq, (vd::v, eq::eq_copy::eqs)
      else
        eq, (v, eq::eqs)
  | _, _ ->
      eq, (v, eq::eqs)

let node funs acc nd =
  let nd, (v, eqs) = Mls_mapfold.node_dec funs (nd.n_local, []) nd in
    { nd with n_local = v; n_equs = eqs  }, acc

let program p =
  let funs = { Mls_mapfold.defaults with eq = eq; node_dec = node } in
  let p, _ = Mls_mapfold.program_it funs ([], []) p in
    p
