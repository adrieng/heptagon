(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* removing switch statements and translation into Minils *)

open Location
open Misc
open Names
open Idents
open Static
open Types
open Clocks
open Format

open Minils
open Mls_utils
open Signature

module Error =
struct
  type error =
    | Ereset_not_var
    | Eunsupported_language_construct

  let message loc kind =
    begin match kind with
      | Ereset_not_var ->
          eprintf "%aOnly variables can be used for resets.@."
            print_location loc
      | Eunsupported_language_construct ->
          eprintf "%aThis construct is not supported by MiniLS.@."
            print_location loc
    end;
    raise Errors.Error
end

module Env =
  (* associate a clock level [base on C1(x1) on ... Cn(xn)] to every *)
  (* local name [x]                                                  *)
  (* then [x] is translated into [x when C1(x1) ... when Cn(xn)]     *)
struct
  type env =
    | Eempty
    | Ecomp of env * IdentSet.t
    | Eon of env * constructor_name * ident

  let empty = Eempty

  let push env tag c = Eon(env, tag, c)

  let add l env =
    Ecomp(env,
          List.fold_left
            (fun acc { Heptagon.v_ident = n } ->
               IdentSet.add n acc) IdentSet.empty l)

  (* sample e according to the clock [base on C1(x1) on ... on Cn(xn)] *)
  let con env x e =
    let rec conrec env =
      match env with
        | Eempty -> Format.eprintf "%s@." (name x); assert false
        | Eon(env, tag, name) ->
            let e, ck = conrec env in
            let ck_tag_name = Con(ck, tag, name) in
            { e with e_desc = Ewhen(e, tag, name); e_ck = ck_tag_name },
            ck_tag_name
        | Ecomp(env, l) ->
            if IdentSet.mem x l then (e, Cbase) else conrec env in
    let e, _ = conrec env in e

  (* a constant [c] is translated into [c when C1(x1) on ... on Cn(xn)] *)
  let const env e =
    let rec constrec env =
      match env with
        | Eempty -> e, Cbase
        | Eon(env, tag, name) ->
            let e, ck = constrec env in
            let ck_tag_name = Con(ck, tag, name) in
            { e with e_desc = Ewhen(e, tag, name); e_ck = ck_tag_name },
            ck_tag_name
        | Ecomp(env, _) -> constrec env in
    let e, _ = constrec env in e
end

(* add an equation *)
let equation locals l_eqs e =
  let n = Idents.fresh "ck" in
  n,
  (mk_var_dec n e.e_ty) :: locals,
  (mk_equation (Evarpat n) e):: l_eqs

(* inserts the definition [x,e] into the set of shared equations *)
let rec add x e shared =
  match shared with
    | [] -> [x, e]
    | (y, e_y) :: s ->
        if x < y then (x, e) :: shared else (y, e_y) :: add x e s

let add_locals ni l_eqs s_eqs s_handlers =
  let rec addrec l_eqs s_eqs s_handlers =
    match s_handlers with
      | [] -> l_eqs, s_eqs
      | (x, e) :: s_handlers ->
          if IdentSet.mem x ni then addrec l_eqs (add x e s_eqs) s_handlers
          else
            addrec ((mk_equation (Evarpat x) e) :: l_eqs)
              s_eqs s_handlers in
  addrec l_eqs s_eqs s_handlers

let translate_var { Heptagon.v_ident = n; Heptagon.v_type = ty;
                    Heptagon.v_loc = loc } =
  mk_var_dec ~loc:loc n ty

let translate_locals locals l =
  List.fold_left (fun locals v -> translate_var v :: locals) locals l

(*transforms [c1, [(x1, e11);...;(xn, e1n)];...;ck, [(x1,ek1);...;(xn,ekn)]] *)
(*into [x1=merge x (c1, e11)...(ck, ek1);...;xn=merge x (c1, e1n)...(ck,ekn)]*)
let switch x ci_eqs_list =
  (* Defensive coherence check *)
  let check ci_eqs_list =
    let rec unique = function
        [] -> true
      | x :: h -> not (List.mem x h) && (unique h) in

    let rec extract eqs_lists =
      match eqs_lists with
        | [] -> [],[]
        | []::eqs_lists' ->
            (* check length *)
            assert (List.for_all (function [] -> true | _ -> false) eqs_lists');
            [],[]
        | ((x,e)::eqs)::eqs_lists' ->
            let firsts,nexts = extract eqs_lists' in
            (x,e)::firsts,eqs::nexts in

    let rec check_eqs eqs_lists =
      match eqs_lists with
        | [] -> ()
        | []::eqs_lists' ->
            (* check length *)
            assert (List.for_all (function [] -> true | _ -> false) eqs_lists')
        | _ ->
            let firsts,nexts = extract eqs_lists in
            (* check all firsts defining same name *)
            if (List.for_all (fun (x,_) -> x = (fst (List.hd firsts))) firsts)
            then ()
            else
              begin
                List.iter
                  (fun (x,_) -> Format.eprintf "|%s|, " (name x))
                  firsts;
                assert false
              end;
            check_eqs nexts in

    let ci,eqs = List.split ci_eqs_list in
    (* constructors uniqueness *)
    assert (unique ci);
    check_eqs eqs in

  let rec split ci_eqs_list =
    match ci_eqs_list with
      | [] | (_, []) :: _ -> [], []
      | (ci, (_, e) :: shared_eq_list) :: ci_eqs_list ->
          let ci_e_list, ci_eqs_list = split ci_eqs_list in
          (ci, e) :: ci_e_list, (ci, shared_eq_list) :: ci_eqs_list in

  let rec distribute ci_eqs_list =
    match ci_eqs_list with
      | [] | (_, []) :: _ -> []
      | (_, (y, { e_ty = ty; e_loc = loc }) :: _) :: _ ->
          let ci_e_list, ci_eqs_list = split ci_eqs_list in
          (y, mk_exp ~ty:ty ~loc:loc (Emerge(x, ci_e_list))) ::
            distribute ci_eqs_list in

  check ci_eqs_list;
  distribute ci_eqs_list

let translate_reset = function
  | Some { Heptagon.e_desc = Heptagon.Evar n } -> Some n
  | Some re -> Error.message re.Heptagon.e_loc Error.Ereset_not_var
  | None -> None

let translate_iterator_type = function
  | Heptagon.Imap -> Imap
  | Heptagon.Ifold -> Ifold
  | Heptagon.Ifoldi -> Ifoldi
  | Heptagon.Imapfold -> Imapfold

let rec translate_op = function
  | Heptagon.Eequal -> Eequal
  | Heptagon.Eifthenelse -> Eifthenelse
  | Heptagon.Efun f -> Efun f
  | Heptagon.Enode f -> Enode f
  | Heptagon.Efield -> Efield
  | Heptagon.Efield_update -> Efield_update
  | Heptagon.Earray_fill -> Earray_fill
  | Heptagon.Eselect -> Eselect
  | Heptagon.Eselect_dyn -> Eselect_dyn
  | Heptagon.Eupdate -> Eupdate
  | Heptagon.Eselect_slice -> Eselect_slice
  | Heptagon.Econcat -> Econcat
  | Heptagon.Earray -> Earray
  | Heptagon.Etuple -> Etuple
  | Heptagon.Earrow ->
      Error.message no_location Error.Eunsupported_language_construct

let translate_app app =
  mk_app ~params:app.Heptagon.a_params
    ~unsafe:app.Heptagon.a_unsafe (translate_op app.Heptagon.a_op)

let rec translate env
    { Heptagon.e_desc = desc; Heptagon.e_ty = ty;
      Heptagon.e_loc = loc } =
  match desc with
    | Heptagon.Econst c ->
        Env.const env (mk_exp ~loc:loc ~ty:ty (Econst c))
    | Heptagon.Evar x ->
        Env.con env x (mk_exp ~loc:loc ~ty:ty (Evar x))
    | Heptagon.Epre(None, e) ->
        mk_exp ~loc:loc ~ty:ty (Efby(None, translate env e))
    | Heptagon.Epre(Some c, e) ->
        mk_exp ~loc:loc ~ty:ty (Efby(Some c, translate env e))
    | Heptagon.Efby ({ Heptagon.e_desc = Heptagon.Econst c }, e) ->
        mk_exp ~loc:loc ~ty:ty (Efby(Some c, translate env e))
    | Heptagon.Estruct f_e_list ->
        let f_e_list = List.map
          (fun (f, e) -> (f, translate env e)) f_e_list in
        mk_exp ~loc:loc ~ty:ty (Estruct f_e_list)
    | Heptagon.Eapp(app, e_list, reset) ->
        mk_exp ~loc:loc ~ty:ty (Eapp (translate_app app,
                                          List.map (translate env) e_list,
                                          translate_reset reset))
    | Heptagon.Eiterator(it, app, n, e_list, reset) ->
        mk_exp ~loc:loc ~ty:ty
          (Eiterator (translate_iterator_type it,
                    translate_app app, n,
                    List.map (translate env) e_list,
                    translate_reset reset))
    | Heptagon.Efby _
    | Heptagon.Elast _ ->
        Error.message loc Error.Eunsupported_language_construct
    | Heptagon.Ewhen (e, c, n) ->
        mk_exp ~loc:loc ~ty:ty (Ewhen (translate env e, c, n))
    | Heptagon.Emerge (n, c_e_list) ->
        mk_exp ~loc:loc ~ty:ty
          (Emerge (n, List.map (fun (c,e) -> c, translate env e) c_e_list))

let rec translate_pat = function
  | Heptagon.Evarpat(n) -> Evarpat n
  | Heptagon.Etuplepat(l) -> Etuplepat (List.map translate_pat l)

let rec rename_pat ni locals s_eqs = function
  | Heptagon.Evarpat(n), ty ->
      if IdentSet.mem n ni then (
        let n_copy = Idents.fresh (sourcename n) in
        Evarpat n_copy,
        (mk_var_dec n_copy ty) :: locals,
        add n (mk_exp ~ty:ty (Evar n_copy)) s_eqs
      ) else
        Evarpat n, locals, s_eqs
  | Heptagon.Etuplepat(l), Tprod l_ty ->
      let l, locals, s_eqs =
        List.fold_right2
          (fun pat ty (p_list, locals, s_eqs) ->
             let pat, locals, s_eqs = rename_pat  ni locals s_eqs (pat,ty) in
             pat :: p_list, locals, s_eqs) l l_ty
          ([], locals, s_eqs) in
      Etuplepat(l), locals, s_eqs
  | _ -> assert false

let all_locals ni p =
  IdentSet.is_empty (IdentSet.inter (Heptagon.vars_pat p) ni)

let rec translate_eq env ni (locals, l_eqs, s_eqs)
    { Heptagon.eq_desc = desc; Heptagon.eq_loc = loc } =
  match desc with
    | Heptagon.Eswitch(e, switch_handlers) ->
        translate_switch_handlers env ni (locals,l_eqs,s_eqs) e switch_handlers
    | Heptagon.Eeq(Heptagon.Evarpat n, e) when IdentSet.mem n ni ->
        locals,
        l_eqs,
        add n (translate env e) s_eqs
    | Heptagon.Eeq(p, e) when all_locals ni p ->
        (* all vars from [p] are local *)
        locals,
        (mk_equation ~loc:loc (translate_pat p) (translate env e)) :: l_eqs,
        s_eqs
    | Heptagon.Eeq(p, e) (* some are local *) ->
        (* transforms [p = e] into [p' = e; p = p'] *)
        let p', locals, s_eqs =
          rename_pat ni locals s_eqs (p, e.Heptagon.e_ty) in
        locals,
        (mk_equation ~loc:loc p' (translate env e)) :: l_eqs,
        s_eqs
    | Heptagon.Epresent _ | Heptagon.Eautomaton _ | Heptagon.Ereset _ ->
        Error.message loc Error.Eunsupported_language_construct

and translate_eqs env ni (locals, local_eqs, shared_eqs) eq_list =
  List.fold_left
    (fun (locals, local_eqs, shared_eqs) eq ->
       translate_eq env ni (locals, local_eqs, shared_eqs) eq)
    (locals, local_eqs, shared_eqs) eq_list

and translate_block env ni (locals, l_eqs)
    { Heptagon.b_local = l; Heptagon.b_equs = eq_list} =
  let env = Env.add l env in
  let locals = translate_locals locals l in
  let locals, local_eqs, shared_eqs =
    translate_eqs env ni (locals, l_eqs, []) eq_list in
  locals, local_eqs, shared_eqs

and translate_switch_handlers env ni (locals, l_eqs, s_eqs) e handlers =
  let rec transrec x ni_handlers (locals, l_eqs, ci_s_eqs_list) handlers =
    match handlers with
        [] -> locals, l_eqs, ci_s_eqs_list
      | { Heptagon.w_name = ci; Heptagon.w_block = b } :: handlers ->
          let locals, l_eqs, s_eqs =
            translate_block (Env.push env ci x) ni_handlers (locals, l_eqs) b in
          transrec x ni_handlers (locals, l_eqs, (ci, s_eqs) :: ci_s_eqs_list)
            handlers in

  let def = function
      [] -> IdentSet.empty
    | { Heptagon.w_block = { Heptagon.b_defnames = env } } :: _ ->
        (* Create set from env *)
        (Idents.Env.fold
           (fun name _ set -> IdentSet.add name set)
           env
           IdentSet.empty) in

  let ni_handlers = def handlers in
  let x, locals, l_eqs = equation locals l_eqs (translate env e) in
  let locals, l_eqs, ci_s_eqs_list =
    transrec x ni_handlers (locals, l_eqs, []) handlers in
  let s_handlers = switch x ci_s_eqs_list in
  let l_eqs, s_eqs = add_locals ni l_eqs s_eqs s_handlers in
  locals, l_eqs, s_eqs

let translate_contract env contract =
  match contract with
    | None -> None, env
    | Some { Heptagon.c_block = { Heptagon.b_local = v;
                                  Heptagon.b_equs = eq_list };
             Heptagon.c_assume = e_a;
             Heptagon.c_enforce = e_g} ->
        let env' = Env.add v env in
        let locals = translate_locals [] v in
        let locals, l_eqs, s_eqs =
          translate_eqs env' IdentSet.empty (locals, [], []) eq_list in
        let l_eqs, _ = add_locals IdentSet.empty l_eqs [] s_eqs in
        let e_a = translate env' e_a in
        let e_g = translate env' e_g in
        Some { c_local = locals;
               c_eq = l_eqs;
               c_assume = e_a;
               c_enforce = e_g },
        env


let node
    { Heptagon.n_name = n; Heptagon.n_input = i; Heptagon.n_output = o;
      Heptagon.n_contract = contract;
      Heptagon.n_block = { Heptagon.b_local = v; Heptagon.b_equs = eq_list };
      Heptagon.n_loc = loc;
      Heptagon.n_params =  params;
      Heptagon.n_params_constraints = params_constr } =
  let env = Env.add o (Env.add i Env.empty) in
  let contract, env = translate_contract env contract in
  let env = Env.add v env in
  let locals = translate_locals [] v in
  let locals, l_eqs, s_eqs =
    translate_eqs env IdentSet.empty (locals, [], []) eq_list in
  let l_eqs, _ = add_locals IdentSet.empty l_eqs [] s_eqs in
  { n_name = n;
    n_input = List.map translate_var i;
    n_output = List.map translate_var o;
    n_contract = contract;
    n_local = locals;
    n_equs = l_eqs;
    n_loc = loc ;
    n_params = params;
    n_params_constraints = params_constr }

let typedec
    {Heptagon.t_name = n; Heptagon.t_desc = tdesc; Heptagon.t_loc = loc} =
  let onetype = function
    | Heptagon.Type_abs -> Type_abs
    | Heptagon.Type_alias ln -> Type_alias ln
    | Heptagon.Type_enum tag_list -> Type_enum tag_list
    | Heptagon.Type_struct field_ty_list -> Type_struct field_ty_list
  in
  { t_name = n; t_desc = onetype tdesc; t_loc = loc }

let const_dec cd =
  { Minils.c_name = cd.Heptagon.c_name;
    Minils.c_value = cd.Heptagon.c_value;
    Minils.c_type = cd.Heptagon.c_type;
    Minils.c_loc = cd.Heptagon.c_loc; }

let program
    { Heptagon.p_modname = modname;
      Heptagon.p_opened = modules;
      Heptagon.p_types = pt_list;
      Heptagon.p_nodes = n_list;
      Heptagon.p_consts = c_list; } =
  { p_modname = modname;
    p_format_version = minils_format_version;
    p_opened = modules;
    p_types = List.map typedec pt_list;
    p_nodes = List.map node n_list;
    p_consts = List.map const_dec c_list}
