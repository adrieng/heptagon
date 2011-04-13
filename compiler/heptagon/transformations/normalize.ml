(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
open Misc
open Names
open Idents
open Location
open Heptagon
open Hept_mapfold
open Types
open Clocks
open Format

(** Normalization pass
    The normal form of the language is given in the manual *)

module Error =
struct
  type error =
    | Eunsupported_language_construct

  let message loc kind =
    begin match kind with
      | Eunsupported_language_construct ->
          eprintf "%aThis construct is not supported by MiniLS.@."
            print_location loc
    end;
    raise Errors.Error
end

let is_stateful e = match e.e_desc with 
  | Efby _ | Epre _ -> true
  | Eapp({ a_op = Enode _ }, _, _) -> true
  | _ -> false

let exp_list_of_static_exp_list se_list =
  let mk_one_const se =
    mk_exp (Econst se) se.se_ty
  in
    List.map mk_one_const se_list

let is_list e = match e.e_desc with 
 | Eapp({ a_op = Etuple }, _, _) 
 | Econst { se_desc = Stuple _ } -> true
 | _ -> false

let e_to_e_list e = match e.e_desc with
  | Eapp({ a_op = Etuple }, e_list, _) -> e_list
  | Econst { se_desc = Stuple se_list } ->
      exp_list_of_static_exp_list se_list
  | _ -> assert false

let flatten_e_list l =
  let flatten = function
    | { e_desc = Eapp({ a_op =  Etuple }, l, _) } -> l
    | e -> [e]
  in
    List.flatten (List.map flatten l)

(** Creates a new equation x = e, adds x to d_list 
    and the equation to eq_list. *)
let equation (d_list, eq_list) e =
  let add_one_var ty d_list =
    let n = Idents.gen_var "normalize" "v" in
    let d_list = (mk_var_dec n ty) :: d_list in
      n, d_list
  in
    match e.e_ty with
      | Tprod ty_list ->
          let var_list, d_list =
            mapfold (fun d_list ty -> add_one_var ty d_list) d_list ty_list in
          let pat_list = List.map (fun n -> Evarpat n) var_list in
          let eq_list = (mk_equation ~stateful:(is_stateful e)
			    (Eeq (Etuplepat pat_list, e))) :: eq_list in
          let e_list = List.map2
            (fun n ty -> mk_exp (Evar n) ty) var_list ty_list in
          let e = Eapp(mk_app Etuple, e_list, None) in
            (d_list, eq_list), e
      | _ ->
          let n, d_list = add_one_var e.e_ty d_list in
          let eq_list = (mk_equation ~stateful:(is_stateful e) 
			    (Eeq (Evarpat n, e))) :: eq_list in
            (d_list, eq_list), Evar n

(* [(e1,...,ek) when C(n) = (e1 when C(n),...,ek when C(n))] *)
let rec whenc context e c n =
  let when_on_c c n e =
    { e with e_desc = Ewhen(e, c, n) }
  in
    if is_list e then (
      let e_list = List.map (when_on_c c n) (e_to_e_list e) in
          context, { e with e_desc = Eapp(mk_app Etuple, e_list, None) }
    ) else
      context, when_on_c c n e

type kind = ExtValue | Any

(** Creates an equation and add it to the context if necessary. *)
let add context expected_kind ({ e_desc = de } as e) =
  let up = match de, expected_kind with
    | (Evar _ | Eapp ({ a_op = Efield }, _, _) | Ewhen _
      | Eapp ({ a_op = Etuple }, _, _) | Econst _) , ExtValue -> false
    | _ , ExtValue -> true
    | _ -> false in
  if up then
    let context, n = equation context e in
      context, { e with e_desc = n }
  else 
    context, e

let rec translate kind context e =
  let context, e = match e.e_desc with
    | Econst _
    | Evar _ -> context, e
    | Epre(v, e1) -> fby kind context e v e1
    | Efby({ e_desc = Econst v }, e1) -> fby kind context e (Some v) e1
    | Estruct l ->
	let translate_field context (f, e) =
	  let context, e = translate ExtValue context e in
            (f, e), context
	in
        let l, context = mapfold translate_field context l in
          context, { e with e_desc = Estruct l }
    | Ewhen(e1, c, n) ->
        let context, e1 = translate kind context e1 in
          whenc context e1 c n
    | Emerge(n, tag_e_list) ->
	merge context e n tag_e_list
    | Eapp({ a_op = Eifthenelse }, [e1; e2; e3], _) ->
        ifthenelse context e e1 e2 e3
    | Eapp(app, e_list, r) ->
        let context, e_list = translate_list ExtValue context e_list in
          context, { e with e_desc = Eapp(app, flatten_e_list e_list, r) }
    | Eiterator (it, app, n, pe_list, e_list, reset) ->
      (* normalize anonymous nodes *)
      (match app.a_op with
        | Enode f when Itfusion.is_anon_node f ->
	    let nd = Itfusion.find_anon_node f in
            let d_list, eq_list = 
	      translate_eq_list nd.n_block.b_local nd.n_block.b_equs in
	    let b = { nd.n_block with b_local = d_list; b_equs = eq_list } in
	    let nd = { nd with n_block = b } in
	      Itfusion.replace_anon_node f nd
        | _ -> () );
        let context, pe_list = translate_list ExtValue context pe_list in
        let context, e_list = translate_list ExtValue context e_list in
        context, { e with e_desc = Eiterator(it, app, n, flatten_e_list pe_list,
                                             flatten_e_list e_list, reset) }
    | Elast _ | Efby _ ->
	Error.message e.e_loc Error.Eunsupported_language_construct
  in add context kind e

and translate_list kind context e_list =
  match e_list with
    | [] -> context, []
    | e :: e_list ->
        let context, e = translate kind context e in
        let context, e_list = translate_list kind context e_list in
          context, e :: e_list

and fby kind context e v e1 =
  let mk_fby c e =
    mk_exp ~loc:e.e_loc (Epre(Some c, e)) e.e_ty in
  let mk_pre e =
    mk_exp ~loc:e.e_loc (Epre(None, e)) e.e_ty in
  let context, e1 = translate ExtValue context e1 in
  match e1.e_desc, v with
    | Eapp({ a_op = Etuple } as app, e_list, r),
      Some { se_desc = Stuple se_list } ->
        let e_list = List.map2 mk_fby se_list e_list in
        let e = { e with e_desc = Eapp(app, e_list, r) } in
          translate kind context e
    | Econst { se_desc = Stuple se_list },
      Some { se_desc = Stuple v_list } ->
        let e_list = List.map2 mk_fby v_list
          (exp_list_of_static_exp_list se_list) in
        let e = { e with e_desc = Eapp(mk_app Etuple, e_list, None) } in
          translate kind context e
    | Eapp({ a_op = Etuple } as app, e_list, r), None ->
        let e_list = List.map mk_pre e_list in
        let e = { e with e_desc = Eapp(app, e_list, r) } in
          translate kind context e
    | Econst { se_desc = Stuple se_list }, None ->
        let e_list = List.map mk_pre (exp_list_of_static_exp_list se_list) in
        let e = { e with e_desc = Eapp(mk_app Etuple, e_list, None) } in
          translate kind context e
    | _ -> context, { e with e_desc = Epre(v, e1) }

(** transforms [if x then e1, ..., en else e'1,..., e'n] 
    into [if x then e1 else e'1, ..., if x then en else e'n]  *)
and ifthenelse context e e1 e2 e3 =
  let context, e1 = translate ExtValue context e1 in
  let context, e2 = translate ExtValue context e2 in
  let context, e3 = translate ExtValue context e3 in
  let mk_ite_list e2_list e3_list =
    let mk_ite e2 e3 = 
      mk_exp ~loc:e.e_loc 
	(Eapp (mk_app Eifthenelse, [e1; e2; e3], None)) e2.e_ty
    in
    let e_list = List.map2 mk_ite e2_list e3_list in
      { e with e_desc = Eapp(mk_app Etuple, e_list, None) }
  in
    if is_list e2 then (
      context, mk_ite_list (e_to_e_list e2) (e_to_e_list e2)
    ) else
      context, { e with e_desc = Eapp (mk_app Eifthenelse, [e1; e2; e3], None) }

(** transforms [merge x (c1, (e11,...,e1n));...;(ck, (ek1,...,ekn))] into
    [merge x (c1, e11)...(ck, ek1),..., merge x (c1, e1n)...(ck, ekn)]    *)
and merge context e x c_e_list =
    let translate_tag context (tag, e) =
      let context, e = translate ExtValue context e in
        (tag, e), context
    in
    let mk_merge x c_list e_list =
      let ty = (List.hd e_list).e_ty in
      let t_e_list = List.map2 (fun t e -> (t,e)) c_list e_list in
	mk_exp ~loc:e.e_loc (Emerge(x, t_e_list)) ty
    in
    let context, x = translate ExtValue context x in
    let c_e_list, context = mapfold translate_tag context c_e_list in
      match c_e_list with
	| [] -> assert false
	| (_,e)::_ ->
	    if is_list e then (
	      let c_list = List.map (fun (t,_) -> t) c_e_list in
	      let e_lists = List.map (fun (_,e) -> e_to_e_list e) c_e_list in
	      let e_list = List.map (mk_merge x c_list) e_lists in
		context, { e with e_desc = Eapp(mk_app Etuple, e_list, None) }
	    ) else
	      context, { e with e_desc = Emerge(x, c_e_list) }

(* applies distribution rules *)
(* [x = v fby e] should verifies that x is local *)
(* [(p1,...,pn) = (e1,...,en)] into [p1 = e1;...;pn = en] *)
and distribute ((d_list, eq_list) as context) eq pat e =
  match pat, e.e_desc with
    | Evarpat(x), Efby _ when not (vd_mem x d_list) ->
        let (d_list, eq_list), n = equation context e in
	let eq = { eq with eq_desc = Eeq(pat, { e with e_desc = n }) } in
          d_list,  eq::eq_list
    | Etuplepat(pat_list), Eapp({ a_op = Etuple }, e_list, _) ->
	let mk_eq pat e = 
	  mk_equation ~stateful:eq.eq_stateful (Eeq (pat, e))
	in
	let dis context eq = match eq.eq_desc with 
	  | Eeq (pat, e) -> distribute context eq pat e 
	  | _ -> assert false
	in
        let eqs = List.map2 mk_eq pat_list e_list in
          List.fold_left dis context eqs
    | _ -> d_list, eq :: eq_list 

and translate_eq context eq = match eq.eq_desc with
  | Eeq (pat, e) -> 
      let context, e = translate Any context e in
	distribute context eq pat e
  | _ -> raise Errors.Fallback

and translate_eq_list d_list eq_list =
  List.fold_left
    (fun context eq -> translate_eq context eq)
    (d_list, []) eq_list

let eq funs context eq =
  let context = translate_eq context eq in
    eq, context

let block funs _ b =
  let _, (v_acc, eq_acc) = Hept_mapfold.block funs ([],[]) b in
    { b with b_local = v_acc@b.b_local; b_equs = eq_acc}, ([], [])

let program p =
  let funs = { defaults with block = block; eq = eq } in
  let p, _ = Hept_mapfold.program funs ([], []) p in
    p
