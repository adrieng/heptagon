(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Gwenaël Delaval                                              *)
(*  Organization : LIG, UJF                                               *)
(*                                                                        *)
(**************************************************************************)

(* Inline code in contracts, collect assume/guarantee of subnodes *)

(* To be done before "completion" and "switch" transformations *)

open Names
open Heptagon
open Hept_utils
open Hept_mapfold
open Initial
open Signature
open Types
open Linearity

(** v_acc is the new local vars which were in lower levels,
    eq_acc contains all the equations *)

let fresh = Idents.gen_var "contracts"

let mk_unique_contract nd =
  let mk_bind vd =
    let id = fresh (Idents.name vd.v_ident) in
    (vd.v_ident, { vd with v_ident = id; v_clock = Clocks.fresh_clock () }) in
  
  let c_local =
    match nd.n_contract with
      None -> []
    | Some { c_block = b } -> b.b_local in
  
  let subst = List.map mk_bind (c_local @ nd.n_input @ nd.n_output) in

  let subst_var_dec _ () vd = (List.assoc vd.v_ident subst, ()) in

  let subst_edesc funs () ed =
    let ed, () = Hept_mapfold.edesc funs () ed in
    let find vn = (List.assoc vn subst).v_ident in
    (match ed with
      | Evar vn -> Evar (find vn)
      | Elast vn -> Elast (find vn)
      | Ewhen (e, cn, vn) -> Ewhen (e, cn, find vn)
      | Emerge (vn, e_l) -> Emerge (find vn, e_l)
      | _ -> ed), ()
  in

  let subst_eqdesc funs () eqd =
    let (eqd, ()) = Hept_mapfold.eqdesc funs () eqd in
    match eqd with
    | Eeq (pat, e) ->
        let rec subst_pat pat = match pat with
          | Evarpat vn -> Evarpat (try (List.assoc vn subst).v_ident
                                   with Not_found -> vn)
          | Etuplepat patl -> Etuplepat (List.map subst_pat patl) in
        (Eeq (subst_pat pat, e), ())
    | _ -> raise Errors.Fallback in

  let funs = { defaults with
                 var_dec = subst_var_dec;
                 eqdesc = subst_eqdesc;
                 edesc = subst_edesc; } in
  fst (Hept_mapfold.node_dec funs () nd)

let exp funs (env, newvars, newequs, contracts) exp =
  let exp, (env, newvars, newequs, contracts) =
    Hept_mapfold.exp funs (env, newvars, newequs, contracts) exp in
  match exp.e_desc with
  | Eapp ({ a_op = (Enode nn | Efun nn); } as op, argl, rso) ->
    begin try
      let add_reset eq = match rso with
        | None -> eq
        | Some x -> mk_equation (Ereset (mk_block [eq], x)) in

      let ni = mk_unique_contract (QualEnv.find nn env) in

      let ci = match ni.n_contract with
          None -> raise Not_found
        | Some c -> c in

      let static_subst =
        List.combine (List.map (fun p -> (local_qn p.p_name)) ni.n_params)
          op.a_params in

      (* Perform [static_exp] substitution. *)
      let ni =
        let apply_sexp_subst_sexp funs () sexp = match sexp.se_desc with
          | Svar s -> ((try List.assoc s static_subst
                        with Not_found -> sexp), ())
          | _ -> Global_mapfold.static_exp funs () sexp in

        let funs =
          { defaults with global_funs =
              { Global_mapfold.defaults with Global_mapfold.static_exp =
                  apply_sexp_subst_sexp; }; } in

        fst (Hept_mapfold.node_dec funs () ni) in

      (* equation "x = e" for inputs *)
      let mk_input_equ vd e = mk_equation (Eeq (Evarpat vd.v_ident, e)) in
      (* output expression "y" *)
      let mk_output_exp vd = mk_exp (Evar vd.v_ident) vd.v_type ~linearity:vd.v_linearity in

      (* equation "y = f(x)" *)
      let eq_app =
        let pat = match ni.n_output with
            [o] -> Evarpat(o.v_ident)
          | ol -> Etuplepat(List.map (fun o -> Evarpat(o.v_ident)) ol) in
        let v_argl = 
          List.map 
            (fun vd -> mk_exp (Evar vd.v_ident) vd.v_type ~linearity:vd.v_linearity)
            ni.n_input in
        mk_equation (Eeq (pat, { exp with e_desc = Eapp (op, v_argl, rso) })) in

      (* variables for assume and guarantee *)
      let v_a = fresh ((shortname nn) ^ "_assume") in
      let v_g = fresh ((shortname nn) ^ "_guarantee") in
      (* equations for assume/guarantee *)
      let eq_a = mk_equation (Eeq (Evarpat v_a, ci.c_assume)) in
      let eq_g = mk_equation (Eeq (Evarpat v_g, ci.c_enforce)) in

      let newvars = ni.n_input @ ci.c_block.b_local @ ni.n_output @ newvars
      and newequs =
        List.map2 mk_input_equ ni.n_input argl
        @ List.map add_reset ci.c_block.b_equs
        @ [ eq_app; eq_a; eq_g ]
        @ newequs 
      and contracts = (v_a,v_g)::contracts in

      (* For clocking reason we cannot create 1-tuples. *)
      let res_e = match ni.n_output with
        | [o] -> mk_output_exp o
        | _ ->
            mk_exp (Eapp ({ op with a_op = Etuple; },
                          List.map mk_output_exp ni.n_output, None)) exp.e_ty
                   ~linearity:exp.e_linearity in

      (res_e, (env, newvars, newequs, contracts))

    with
      | Not_found ->
        exp, (env, newvars, newequs, contracts)
    end
  | _ -> exp, (env, newvars, newequs, contracts)

let block funs (env, newvars, newequs, contracts) blk =
  let (blk, (env, newvars', newequs', contracts')) =
    Hept_mapfold.block funs (env, [], [], contracts) blk in
  ({ blk with b_local = newvars' @ blk.b_local; b_equs = newequs' @ blk.b_equs; },
   (env, newvars, newequs, contracts'))

let not_exp e = mk_exp (mk_op_app (Efun pnot) [e]) tbool ~linearity:Ltop

let (&&&) e1 e2 = mk_exp (mk_op_app (Efun pand) [e1;e2]) tbool ~linearity:Ltop
let (|||) e1 e2 = mk_exp (mk_op_app (Efun por) [e1;e2]) tbool ~linearity:Ltop

let (=>) e1 e2 = (not_exp e1) ||| e2

let var_exp v = mk_exp (Evar v) tbool ~linearity:Ltop

let true_exp = mk_exp (Econst (mk_static_bool true)) tbool ~linearity:Ltop

let mk_vd_bool v = mk_var_dec ~last:(Last (Some (mk_static_bool true))) v tbool ~linearity:Ltop

let node_dec funs (env, newvars, newequs, contracts) nd =
  let nd, (env, newvars, newequs, contracts) =
    Hept_mapfold.node_dec funs (env, newvars, newequs, contracts) nd in
  
  (* Build assume and guarantee parts from contract list (list of
     ident pairs (v_a,v_g)). Returns also a list of variable
     declarations. *)
  let rec build_contract contracts =
    match contracts with
      [] -> true_exp, true_exp, []
    | [(v_a,v_g)] ->
        let e_a = var_exp v_a in
        let e_g = var_exp v_g in
        (* assume part : e_a => e_g ; guarantee part : e_a *)
        (e_a => e_g), e_a, [mk_vd_bool v_a; mk_vd_bool v_g]
    | (v_a,v_g)::l ->
        let e_a_l,e_g_l,vd_l = build_contract l in
        let e_a = var_exp v_a in
        let e_g = var_exp v_g in
        ((e_a => e_g) &&& e_a_l), (e_a &&& e_g_l),
        ((mk_vd_bool v_a) :: (mk_vd_bool v_g) :: vd_l)
  in

  let assume_loc, enforce_loc, vd_contracts = build_contract contracts in
  let nc =
    match nd.n_contract, contracts with
      c,[] -> c
    | None,_::_ -> 
        Some { c_assume = true_exp;
               c_enforce = true_exp;
               c_assume_loc = assume_loc;
               c_enforce_loc = enforce_loc;
               c_controllables = [];
               c_block = mk_block ~stateful:false [] }
    | Some c,_::_ ->
        Some { c with
                 c_assume_loc = assume_loc;
                 c_enforce_loc = enforce_loc } in
  let nd = 
    { nd with
        n_contract = nc;
        n_block =
        { nd.n_block with 
            b_local = newvars @ vd_contracts @ nd.n_block.b_local;
            b_equs = newequs @ nd.n_block.b_equs } } in
  let env = QualEnv.add nd.n_name nd env in
   nd, (env, [], [], [])

let program p =
  let funs =
    { defaults with exp = exp; block = block; node_dec = node_dec; eq = eq; } in
  let (p, (_, newvars, newequs, contracts)) =
    Hept_mapfold.program funs (QualEnv.empty, [], [], []) p in
  assert (newvars = []);
  assert (newequs = []);
  assert (contracts = []);
  p

