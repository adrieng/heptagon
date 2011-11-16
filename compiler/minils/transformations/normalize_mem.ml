open Idents
open Signature
open Minils
open Mls_mapfold
open Mls_utils

(**  Adds an extra equation for outputs that are also memories.
     For instance, if o is an output, then:
       o = v fby e
     becomes
       mem_o = v fby e;
       o = mem_o

     We also need to add one copy if two (or more) registers are defined by each other, eg:
       x = v fby y;
       y = v fby x;
     becomes
       mem_x = v fby y;
       x = mem_x;
       y = v fby x
*)

let normalize_outputs = ref true

(** Builds the initial environment, that maps any register to the ident on the right hand side.
    For outputs that are also registers, if normalize_outputs is true,
    they are mapped to themselves to force the copy (made necessary by the calling convention).
    Other variables are mapped to None. *)
let build_env nd =
  let add_none env l = List.fold_left (fun env vd -> Env.add vd.v_ident None env) env l in
  let add_eq env eq = match eq.eq_lhs, eq.eq_rhs.e_desc with
    | Evarpat x, Efby (_, w) -> Env.add x (ident_of_extvalue w) env
    | _, _ ->
       List.fold_left (fun env id -> Env.add id None env) env (Vars.def [] eq)
  in
  let env = add_none Env.empty nd.n_input in
  let env = List.fold_left add_eq env nd.n_equs in
  let env =
    if !normalize_outputs then
      List.fold_left (fun env vd -> Env.add vd.v_ident (Some vd.v_ident) env) env nd.n_output
    else
      env
  in
  env

let rec depends_on x y env =
  match Env.find y env with
    | None -> false
    | Some z ->
      if ident_compare x z = 0 then true
      else if ident_compare y z = 0 then false
      else depends_on x z env

let eq _ (env, vds, v, eqs) eq = match eq.eq_lhs, eq.eq_rhs.e_desc with
  | Evarpat x, Efby (_, _) when depends_on x x env ->
        let vd = vd_find x vds in
        let x_mem = Idents.gen_var "normalize_mem" ("mem_"^(Idents.name x)) in
        let vd_mem = { vd with v_ident = x_mem } in
        let exp_mem_x = mk_extvalue_exp vd.v_clock vd.v_type
          ~clock:vd.v_clock ~linearity:vd.v_linearity (Wvar x_mem) in
        (* mem_o = v fby e *)
        let eq_copy = { eq with eq_lhs = Evarpat x_mem } in
        (* o = mem_o *)
        let eq = { eq with eq_rhs = exp_mem_x } in
        (* remove the dependency in env *)
        let env = Env.add x None env in
        eq, (env, vds, vd_mem::v, eq::eq_copy::eqs)
  | _, _ ->
      eq, (env, vds, v, eq::eqs)

(* Leave contract unchanged (no output defined in it) *)
let contract _ acc c = c, acc

let node funs acc nd =
  let env = build_env nd in
  let nd, (_, _, v, eqs) =
    Mls_mapfold.node_dec funs (env, nd.n_local @ nd.n_output, [], []) nd
  in
  (* return updated node *)
  { nd with n_local = v @ nd.n_local; n_equs = List.rev eqs }, acc

let program p =
  let funs = { Mls_mapfold.defaults with
    eq = eq; node_dec = node; contract = contract } in
  let p, _ = Mls_mapfold.program_it funs (Env.empty, [], [], []) p in
    p
