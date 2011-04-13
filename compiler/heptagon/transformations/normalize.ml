(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
open Misc
open Initial
open Names
open Idents
open Signature
open Heptagon
open Types
open Clocks


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

let is_list e = match e.e_desc with 
 | Eapp({ a_op = Etuple }, e_list, _) 
 | Econst { se_desc = Stuple se_list } -> true
 | _ -> false

let e_to_e_list e = match e.e_desc with
  | Eapp({ a_op = Etuple }, e_list, _) -> e_list
  | Econst { se_desc = Stuple se_list } ->
      exp_list_of_static_exp_list se_list

let flatten_e_list l =
  let flatten = function
    | { e_desc = Eapp({ a_op =  Etuple }, l, _) } -> l
    | e -> [e]
  in
    List.flatten (List.map flatten l)

let equation (d_list, eq_list) e =
  let add_one_var ty d_list =
    let n = Idents.gen_var "normalize" "v" in
    let d_list = (mk_var_dec ~clock:e.e_ck n ty) :: d_list in
      n, d_list
  in
    match e.e_ty with
      | Tprod ty_list ->
          let var_list, d_list =
            mapfold (fun d_list ty -> add_one_var ty d_list) d_list ty_list in
          let pat_list = List.map (fun n -> Evarpat n) var_list in
          let eq_list = (mk_equation (Etuplepat pat_list) e) :: eq_list in
          let e_list = List.map2
            (fun n ty -> mk_exp ~ty:ty (Evar n)) var_list ty_list in
          let e = Eapp(mk_app Etuple, e_list, None) in
            (d_list, eq_list), e
      | _ ->
          let n, d_list = add_one_var e.e_ty d_list in
          let eq_list = (mk_equation (Evarpat n) e) :: eq_list in
            (d_list, eq_list), Evar n

(* [(e1,...,ek) when C(n) = (e1 when C(n),...,ek when C(n))] *)
let rec whenc context e c n =
  let when_on_c c n e =
    { e with e_desc = Ewhen(e, c, n); e_ck = Con(e.e_ck, c, n) }
  in
    if is_list e then (
      let e_list = List.map (when_on_c c n) (e_to_e_list e) in
          context, { e with e_desc = Eapp (app, e_list, r);
                            e_ck = Con(e.e_ck, c, n) }
    ) else
      context, when_on_c c n e

let const e c =
  let rec const = function
    | Cbase | Cvar { contents = Cindex _ } -> c
    | Con(ck_on, tag, x) ->
        Ewhen({ e with e_desc = const ck_on; e_ck = ck_on }, tag, x)
    | Cvar { contents = Clink ck } -> const ck in
  const e.e_ck

type kind = ExtValue | Any

let add context expected_kind ({ e_desc = de } as e) =
  let up = match de, expected_kind with
    | (Evar _ | Eapp ({ a_op = Efield }, _, _) | Ewhen _
      | Eapp ({ a_op = Etuple }, _, _) | Econst) , ExtValue -> false
    | _ , ExtValue -> true
    | _ -> false in
  if up then
    let context, n = equation context e in
      context, { e with e_desc = n }
  else 
    context, e

let rec translate kind context e =
  let context, e = match e.e_desc with
    | Econst c -> context, { e with e_desc = const e (Econst c) }
    | Evar _ -> context, e
    | Epre(v, e1) -> fby kind context e v e1
    | Efby({ e_desc = Econst v }, e1) -> fby kind context e (Some v) e1
    | Estruct l ->
	let translate_field (f, e) context =
	  let context, e = translate ExtValue context e in
            context, (f, e)
	in
        let context, l = mapfold translate_field context l in
          context, { e with e_desc = Estruct l }
    | Ewhen(e1, c, n) ->
        let context, e1 = translate kind context e1 in
          whenc context e1 c n
    | Emerge(n, tag_e_list) ->
	merge context n tag_e_list
    | Eapp({ a_op = Eifthenelse }, [e1; e2; e3], _) ->
        ifthenelse context e1 e2 e3
    | Eapp(app, e_list, r) ->
        let context, e_list = translate_list ExtValue context e_list in
          context, { e with e_desc = Eapp(app, flatten_e_list e_list, r) }
    | Eiterator (it, app, n, pe_list, e_list, reset) ->
      (* normalize anonymous nodes *)
      (match app.a_op with
        | Enode f when Itfusion.is_anon_node f ->
	    let nd = Itfusion.find_anon_node f in
            let d_list, eq_list = translate_eq_list nd.n_local nd.n_equs in
	    let nd = { nd with n_equs = eq_list; n_local = d_list } in
	      Itfusion.replace_anon_node f nd
        | _ -> () );
        let context, pe_list = translate_list ExtValue context pe_list in
        let context, e_list = translate_list ExtValue context e_list in
        context, { e with e_desc = Eiterator(it, app, n, flatten_e_list pe_list,
                                             flatten_e_list e_list, reset) }
    | Elast _ | Efby _ -> message e.e_loc Eunsupported_language_construct
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
    mk_exp ~ty:e.e_ty ~loc:e.e_loc (Efby(Some c, e)) in
  let mk_pre e =
    mk_exp ~ty:e.e_ty ~loc:e.e_loc (Efby(None, e)) in
  let e1 = translate ExtValue context e1 in
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
        let e = { e with e_desc = Eapp(app, e_list, r) } in
          translate kind context e
    | _ -> context, { e with e_desc = Efby(v, e1) }

(** transforms [if x then e1, ..., en else e'1,..., e'n] 
    into [if x then e1 else e'1, ..., if x then en else e'n]  *)
and ifthenelse context e e1 e2 e3 =
  let context, e1 = translate ExtValue context e1 in
  let context, e2 = translate ExtValue context e2 in
  let context, e3 = translate ExtValue context e3 in
  let mk_ite_list e2_list e3_list =
    let mk_ite e2 e3 = 
      mk_exp ~ty:e2.e_ty ~loc:e.e_loc (Eifthenelse(e1, e2, e3)) 
    in
    let e_list = List.map2 mk_ite e2_list e3_list in
      { e with e_desc = Eapp(mk_app Etuple, e_list, None) }
  in
    if is_list e2 then 
      context, mk_ite_list context (e_to_e_list e2) (e_to_e_list e2)
    else
      context, { e with e_desc = Eifthenelse(e1, e2, e3)}

(** transforms [merge x (c1, (e11,...,e1n));...;(ck, (ek1,...,ekn))] into
    [merge x (c1, e11)...(ck, ek1),..., merge x (c1, e1n)...(ck, ekn)]    *)
and merge context e x c_e_list =
    let translate_tag (tag, e) context =
      let context, e = translate ExtValue context e in
        context, (tag, e)
    in
    let mk_merge x c_list e_list =
      let ty = (hd e_list).e_e_ty in
      let t_e_list = List.map2 (fun t e -> (t,e)) c_list e_list in
	mk_exp ~ty:ty ~loc:e.e_loc (Emerge(x, t_e_list))
    in
    let context, x = translate ExtValue context x in
    let context, c_e_list = mapfold translate_tag context ta_list in
      match c_e_list with
	| [] -> assert false
	| (_,e)::_ ->
	    if is_list e then 
	      let c_list = List.map (fun (t,_) -> t) c_e_list in
	      let e_lists = List.map (fun (_,e) -> e_to_e_list e) c_e_list in
	      let e_list = List.map (mk_merge x c_list) e_lists in
		context, { e with e_desc = Eapp(mk_app Etuple, e_list, None) }
	    else
	      context, { e with e_desc = Emerge(x, c_e_list) }

(* applies distribution rules *)
(* [x = v fby e] should verifies that x is local *)
(* [(p1,...,pn) = (e1,...,en)] into [p1 = e1;...;pn = en] *)
and distribute ((d_list, eq_list) as context) pat e =
  match pat, e.e_desc with
    | Evarpat(x), Efby _ when not (vd_mem x d_list) ->
        let (d_list, eq_list), n = equation context e in
          d_list,
        { eq with eq_rhs = { e with e_desc = n } } :: eq_list
    | Etuplepat(pat_list), Eapp({ a_op = Etuple }, e_list, _) ->
        let eqs = List.map2 mk_equation pat_list e_list in
          List.fold_left distribute context eqs
    | _ -> d_list, Eeq(pat, e) :: eq_list 

and translate_eq context eq = match eq with
  | Eeq (pat, e) -> 
      let context, e = translate Any context e in
	distribute context pat e
  | _ -> raise Fallback

let block funs _ b =
  let _, (v_acc, eq_acc) = Hept_mapfold.block funs ([],[]) b in
    { b with b_local = v_acc@b.b_local; b_equs = eq_acc}, ([], [])

let program p =
  let funs = { defaults with eq = translate_eq; } in
  let p, _ = Hept_mapfold.program funs ([], []) p in
    p
