open Idents
open Signature
open Clocks
open Minils

(**  Adds extra equations for the oversampler :

    A node [. on c(v) -> . on c(v)] when v is a local variable of the node,
    will be given the signature [. -> .] with [n_base_ck = . on c(v)]

    The generated code will be :
[
    do
      {usual step code}+ __node_big_step = merge v (c -> true) (c-> false)
    while not __node_big_step
]
    This new variable __node_oversampling is needed
    to deal with [c] being a memory or a var transparently.

    Moreover, if [n_base_ck = . on c on c'],
      __node_big_step will be [merge c c' false].
    And if [n_base_ck = . on c on c' on c''],
      __node_big_step will be [merge c (merge c' c'' false) false ].

    After this pass, it may be that [n_base_id = Some __node_big_step],
    __node_big_step is also added to the outputs,
    since for the optimization and code generation,
    it has to be considered as an output.
    /!\ This is a dummy output, it is only in the node output, not in the signature.
*)


(** From [v] [(c,w)] returns the expression for [merge v (c -> w) (c'-> false)...(c''->false)] *)
let gen_merge v (c, w) =
  let ck, ck_c = match ck_repr w.w_ck with
    | Con (ck, wc, wv) when wc=c & wv = v ->
        ck, (fun c' -> Con(ck, c', v))
    | _ -> Misc.internal_error "gen_merge wrong w clock"
  in
  let false_cases =
    let t = Modules.find_type (Modules.find_constrs c) in
    let c_false_list = match t with
      | Tenum c_l -> List.filter (fun c'-> not (c = c')) c_l
      | _ -> Misc.internal_error "Oversampler wrong type of constructor"
    in
    List.map (fun c -> (c, extvalue_false (ck_c c))) c_false_list
  in
  mk_exp Cbase Initial.tbool
         ~linearity:Linearity.Ltop ~ct:(Ck ck) (Emerge (v, (c,w)::false_cases))


(** returns [new_eqs, new_vds, base_vd], base_vd is not in new_vds, and is an option :
    if [ck] is base, return [base_vd = None] *)
let rec gen_base (new_eqs,new_vds) super_base_vd super_ck = match ck_repr super_ck with
  | Cbase -> (new_eqs, new_vds, super_base_vd)
  | Con (ck, c, v) ->
      let base_id = Idents.gen_var "normalize_mem" "__node_big_step" in
      let base_vd = mk_var_dec ~is_memory:false base_id Initial.tbool Linearity.Ltop ck in
      let super_base_w = match super_base_vd with
        | None -> extvalue_true super_ck
        | Some super_base_vd -> mk_vd_extvalue super_base_vd
      in
      let base_exp = gen_merge v (c, super_base_w) in
      let base_eq = mk_equation false (Evarpat base_id) base_exp in
      gen_base (base_eq::new_eqs, base_vd::new_vds) (Some base_vd) ck
  | _ -> Misc.internal_error "Oversampling clock not on base"


let node_dec _ () nd =
  let base_ck = nd.n_base_ck in
  let new_eqs, new_vds, base_vd = gen_base (nd.n_equs,nd.n_local) None base_ck in
  let new_vds, outputs = match base_vd, new_vds with
    | None, _ -> new_vds, nd.n_output
    | Some base_vd, _::new_vds -> (* transfer base_vd from new_vds to output_vds *)
        new_vds, base_vd::nd.n_output
    | _ -> Misc.internal_error "Oversampler should have base vd in new_vds"
  in
  let node = { nd with
    n_output = outputs;
    n_local = new_vds;
    n_equs = new_eqs;
    n_base_id = base_vd }
  in
  Mls_utils.update_node_signature node;
  node, ()

let program p =
  let funs = { Mls_mapfold.defaults with Mls_mapfold.node_dec = node_dec } in
  let p, _ = Mls_mapfold.program_it funs () p in
  p
