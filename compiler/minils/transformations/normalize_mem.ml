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

     We also need to add one copy if two registers are defined by each other, eg:
       x = v fby y;
       y = v fby x;
     becomes
       mem_x = v fby y;
       x = mem_x;
       y = v fby x
*)

let memory_vars_vds nd =
  let build env l =
    List.fold_left (fun env vd -> Env.add vd.v_ident vd env) env l
  in
  let env = build Env.empty nd.n_output in
  let env = build env nd.n_local in
  let mem_var_tys = Mls_utils.node_memory_vars nd in
  List.map (fun (x, _) -> Env.find x env) mem_var_tys

let copies_done = ref []
let add_copy x y =
  copies_done := (x, y) :: !copies_done
let clear_copies () =
  copies_done := []
let is_copy_done x y =
  List.mem (x, y) !copies_done

(* If x and y are both registers, only create one copy *)
let should_be_normalized outputs mems x w = match w.w_desc with
  | Wvar y ->
    add_copy x y;
    (vd_mem x outputs) or (vd_mem x mems && not (is_copy_done y x))
  | _ ->
    (vd_mem x outputs) or (vd_mem x mems)

let find_vd x outputs mems =
  if vd_mem x outputs then
    vd_find x outputs
  else
    vd_find x mems

let eq _ (outputs, mems, v, eqs) eq = match eq.eq_lhs, eq.eq_rhs.e_desc with
  | Evarpat x, Efby (_, w) when should_be_normalized outputs mems x w ->
        let vd = find_vd x outputs mems in
        let x_mem = Idents.gen_var "normalize_mem" ("mem_"^(Idents.name x)) in
        let vd_mem = { vd with v_ident = x_mem } in
        let exp_mem_x = mk_extvalue_exp vd.v_clock vd.v_type
          ~clock:vd.v_clock ~linearity:vd.v_linearity (Wvar x_mem) in
        (* mem_o = v fby e *)
        let eq_copy = { eq with eq_lhs = Evarpat x_mem } in
        (* o = mem_o *)
        let eq = { eq with eq_rhs = exp_mem_x } in
        eq, (outputs, mems, vd_mem::v, eq::eq_copy::eqs)
  | _, _ ->
      eq, (outputs, mems, v, eq::eqs)

(* Leave contract unchanged (no output defined in it) *)
let contract funs acc c = c, acc

let node funs acc nd =
  clear_copies ();
  let nd, (_, _, v, eqs) =
    Mls_mapfold.node_dec funs (nd.n_output, memory_vars_vds nd, nd.n_local, []) nd
  in
  (* return updated node *)
  { nd with n_local = v; n_equs = List.rev eqs }, acc

let program p =
  let funs = { Mls_mapfold.defaults with
    eq = eq; node_dec = node; contract = contract } in
  let p, _ = Mls_mapfold.program_it funs ([], [], [], []) p in
    p
