(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* type checking *)

(* $Id$ *)

open Misc
open Names
open Ident
open Location
open Signature
open Modules
open Initial
open Static
open Types
open Heptagon
open Hept_mapfold

type value = { ty: ty; mutable last: bool }

type error =
  | Emissing of name
  | Emissingcase of name
  | Eundefined of name
  | Elast_undefined of name
  | Eshould_be_last of name
  | Etype_clash of ty * ty
  | Earity_clash of int * int
  | Ealready_defined of name
  | Eshould_be_a_node of longname
  | Enon_exaustive
  | Estate_clash
  | Epartial_switch of name
  | Etoo_many_outputs
  | Esome_fields_are_missing
  | Esubscripted_value_not_an_array of ty
  | Earray_subscript_should_be_const
  | Eundefined_const of longname
  | Econstraint_solve_failed of size_constraint
  | Etype_should_be_static of ty
  | Erecord_type_expected of ty
  | Eno_such_field of ty * longname
  | Eempty_record
  | Eempty_array

exception Unify
exception TypingError of error

let error kind = raise (TypingError(kind))

let message loc kind =
  begin match kind with
    | Emissing(s) ->
        Printf.eprintf "%aNo equation is given for name %s.\n"
          output_location loc
          s;
    | Emissingcase(s) ->
        Printf.eprintf "%aCase %s not defined.\n"
          output_location loc
          s;
    | Eundefined(s) ->
        Printf.eprintf "%aThe name %s is unbound.\n"
          output_location loc
          s;
    | Elast_undefined(s) ->
        Printf.eprintf "%aThe name %s does not have a last value.\n"
          output_location loc
          s;
    | Eshould_be_last(s) ->
        Printf.eprintf "%aOnly the last value of %s can be accessed.\n"
          output_location loc
          s;
    | Etype_clash(actual_ty, expected_ty) ->
        Printf.eprintf "%aType Clash: this expression has type %a, \n\
            but is expected to have type %a.\n"
          output_location loc
          Hept_printer.ptype actual_ty
          Hept_printer.ptype expected_ty
    | Earity_clash(actual_arit, expected_arit) ->
        Printf.eprintf "%aType Clash: this expression expects %d arguments,\n\
            but is expected to have %d.\n"
          output_location loc
          expected_arit actual_arit
    | Ealready_defined(s) ->
        Printf.eprintf "%aThe name %s is already defined.\n"
          output_location loc
          s
    | Enon_exaustive ->
        Printf.eprintf "%aSome constructors are missing in this \
                        pattern/matching.\n"
          output_location loc
    | Eshould_be_a_node(s) ->
        Printf.eprintf "%a%s should be a combinatorial function.\n"
          output_location loc
          (fullname s)
    | Estate_clash ->
        Printf.eprintf
          "%aOnly stateless expressions should appear in a function.\n"
          output_location loc
    | Epartial_switch(s) ->
        Printf.eprintf
          "%aThe case %s is missing.\n"
          output_location loc
          s
    | Etoo_many_outputs ->
        Printf.eprintf
          "%aA function may only returns a basic value.\n"
          output_location loc
    | Esome_fields_are_missing ->
        Printf.eprintf
          "%aSome fields are missing.\n"
          output_location loc
    | Esubscripted_value_not_an_array  ty ->
        Printf.eprintf
          "%aSubscript used on a non array type : %a.\n"
          output_location loc
          Hept_printer.ptype ty
    | Earray_subscript_should_be_const ->
        Printf.eprintf
          "%aSubscript has to be a static value.\n"
          output_location loc
    | Eundefined_const ln ->
        Printf.eprintf
          "%aThe const name '%s' is unbound.\n"
          output_location loc
          (fullname ln)
    | Econstraint_solve_failed c ->
        Printf.eprintf
          "%aThe following constraint cannot be satisified:\n %a.\n"
          output_location loc
          psize_constraint c
    | Etype_should_be_static ty ->
        Printf.eprintf
          "%aThis type should be static : %a.\n"
          output_location loc
          Hept_printer.ptype ty
    | Erecord_type_expected ty ->
        Printf.eprintf
          "%aA record was expected (found %a).\n"
          output_location loc
          Hept_printer.ptype ty
    | Eno_such_field (ty, f) ->
        Printf.eprintf
          "%aThe record type '%a' does not have a '%s' field.\n"
          output_location loc
          Hept_printer.ptype ty
          (shortname f)
    | Eempty_record ->
        Printf.eprintf
          "%aThe record is empty.\n"
          output_location loc
    | Eempty_array ->
        Printf.eprintf
          "%aThe array is empty.\n"
          output_location loc
  end;
  raise Error

let add_value f signature =
  try add_value f signature with Already_defined -> error (Ealready_defined f)
let add_type f type_def =
  try add_type f type_def with Already_defined -> error (Ealready_defined f)
let add_constr f ty_res =
  try add_constr f ty_res with Already_defined -> error (Ealready_defined f)
let add_struct f fields =
  try add_struct f fields with Already_defined -> error (Ealready_defined f)
let add_field f n =
  try add_field f n with Already_defined -> error (Ealready_defined f)
let add_const f n =
  try add_const f n with Already_defined -> error (Ealready_defined f)

let find_value f =
  try find_value f with Not_found -> error (Eundefined(fullname f))
let find_type f =
  try find_type f with Not_found -> error (Eundefined(fullname f))
let find_constr c =
  try find_constr c with Not_found -> error (Eundefined(fullname c))
let find_field c =
  try find_field c with Not_found -> error (Eundefined(fullname c))
let find_struct c =
  try find_struct c with Not_found -> error (Eundefined(fullname c))

let (curr_size_constr : size_constraint list ref) = ref []
let add_size_constraint c =
  curr_size_constr := c::(!curr_size_constr)
let get_size_constraint () =
  let l = !curr_size_constr in
  curr_size_constr := [];
  l

let get_number_of_fields ty =
  let { info = tydesc } =
    match ty with
      | Tid(f) -> find_type f
      | _ -> assert false in
  match tydesc with
    | Tstruct l -> List.length l
    | _ -> assert false

let element_type ty =
  match ty with
    | Tarray (ty, _) -> ty
    | _ -> error (Esubscripted_value_not_an_array ty)

let array_size ty =
  match ty with
    | Tarray (_, e) -> e
    | _ -> error (Esubscripted_value_not_an_array ty)

let rec unify t1 t2 =
  match t1, t2 with
    | b1, b2 when b1 = b2 -> ()
    | Tprod t1_list, Tprod t2_list ->
        (try
           List.iter2 unify t1_list t2_list
         with
             _ -> raise Unify
        )
    | Tarray (ty1, e1), Tarray (ty2, e2) ->
        add_size_constraint (Cequal(e1,e2));
        unify ty1 ty2
    | _ -> raise Unify

let unify t1 t2 =
  try unify t1 t2 with Unify -> error (Etype_clash(t1, t2))

let less_than statefull = if not statefull then error Estate_clash

let is_statefull_eq_desc eqd =
  let edesc funs _ ed = match ed with
    | Elast _ | Efby _ | Epre _ -> ed, true
    | Eapp({ a_op = (Enode _ | Earrow) }, _, _) -> ed, true
    | _ -> raise Misc.Fallback
  in
  let funs = { Hept_mapfold.defaults with edesc = edesc } in
  let _, is_statefull = Hept_mapfold.eqdesc_it funs false eqd in
    is_statefull

let kind f statefull
    { node_inputs = ty_list1;
      node_outputs = ty_list2;
      node_statefull = n } =
  let ty_of_arg v = v.a_type in
  let op = if n then Enode f else Efun f in
    if n & not(statefull) then error (Eshould_be_a_node f)
    else op, List.map ty_of_arg ty_list1, List.map ty_of_arg ty_list2

let prod = function
  | []      -> assert false
  | [ty]    -> ty
  | ty_list -> Tprod ty_list

let typ_of_name h x =
  try
    let { ty = ty } = Env.find x h in ty
  with
      Not_found -> error (Eundefined(sourcename x))

let typ_of_varname h x =
  try
    let { ty = ty;last = last } = Env.find x h in
    (* Don't understand that - GD 15/02/2009 *)
    (*     if last then error (Eshould_be_last(x)); *)
    ty
  with
      Not_found -> error (Eundefined(sourcename x))

let typ_of_last h x =
  try
    let { ty = ty; last = last } = Env.find x h in
    if not last then error (Elast_undefined(sourcename x));
    (* v.last <- true;*)
    ty
  with
      Not_found -> error (Eundefined(sourcename x))

let desc_of_ty = function
  | Tid n when n = pbool  -> Tenum ["true";"false"]
  | Tid ty_name ->
      let { info = tydesc } = find_type ty_name in tydesc
  | _  -> Tabstract
let set_of_constr = function
  | Tabstract | Tstruct _  -> assert false
  | Tenum tag_list -> List.fold_right S.add tag_list S.empty

let name_mem n env =
  let check_one id _ acc =
    ((name id) = n) or acc
  in
  Env.fold check_one env false

let rec simplify_type = function
  | Tid _ as t -> t
  | Tarray(ty, e) ->
      Tarray(simplify_type ty, simplify NamesEnv.empty e)
  | Tprod l ->
      Tprod (List.map simplify_type l)

let simplify_type loc ty =
  try
    simplify_type ty
  with
      Instanciation_failed -> message loc (Etype_should_be_static ty)

let build_subst names values =
  List.fold_left2 (fun m { p_name = n } v -> NamesEnv.add n v m)
    NamesEnv.empty names values

let rec subst_type_vars m = function
  | Tarray(ty, e) -> Tarray(subst_type_vars m ty, static_exp_subst m e)
  | Tprod l -> Tprod (List.map (subst_type_vars m) l)
  | t -> t

let equal expected_tag_list actual_tag_list =
  if not (List.for_all
            (fun tag -> List.mem tag actual_tag_list) expected_tag_list)
  then error Enon_exaustive

(** Add two sets of names provided they are distinct *)
let add env1 env2 =
  Env.fold
    (fun elt ty env ->
       if not (Env.mem elt env)
       then Env.add elt ty env
       else error (Ealready_defined(sourcename elt))) env1 env2

(** Checks that constructors are included in constructor list from type
    def and returns the difference *)
let included_const s1 s2 =
  S.iter
    (fun elt -> if not (S.mem elt s2) then error (Emissingcase(elt)))
    s1

let diff_const defined_names local_names =
  included_const local_names defined_names;
  S.diff defined_names local_names

(** Checks that local_names are included in defined_names and returns
    the difference *)
let included_env s1 s2 =
  Env.iter
    (fun elt _ -> if not (Env.mem elt s2) then error (Emissing(sourcename elt)))
    s1

let diff_env defined_names local_names =
  included_env local_names defined_names;
  Env.diff defined_names local_names

(** [merge [set1;...;setn]] returns a set of names defined in every seti
    and only partially defined names *)
let rec merge local_names_list =
  let two s1 s2 =
    let total, partial = Env.partition (fun elt -> Env.mem elt s2) s1 in
    let partial =
      Env.fold (fun elt ty env ->
                  if not (Env.mem elt total) then Env.add elt ty env
                  else env)
        s2 partial in
    total, partial in
  match local_names_list with
    | [] -> Env.empty, Env.empty
    | [s] -> s, Env.empty
    | s :: local_names_list ->
        let total, partial1 = merge local_names_list in
        let total, partial2 = two s total in
        total, Env.union partial1 partial2

(** Checks that every partial name has a last value *)
let all_last h env =
  Env.iter
    (fun elt _ ->
       if not (Env.find elt h).last
       then error (Elast_undefined(sourcename elt)))
    env

let last = function | Var -> false | Last _ -> true

(** Checks that a field is not defined twice in a list
    of field name, exp.*)
let check_field_unicity l =
  let add_field acc (f,e) =
    if S.mem (shortname f) acc then
      message e.e_loc (Ealready_defined (fullname f))
    else
      S.add (shortname f) acc
  in
  ignore (List.fold_left add_field S.empty l)

(** Checks that a field is not defined twice in a list
    of field name, exp.*)
let check_static_field_unicity l =
  let add_field acc (f,se) =
    if S.mem (shortname f) acc then
      message se.se_loc (Ealready_defined (fullname f))
    else
      S.add (shortname f) acc
  in
  ignore (List.fold_left add_field S.empty l)

(** @return the qualified name and list of fields of
    the type with name [n].
    Prints an error message if the type is not a record type.
    [loc] is the location used for error reporting.*)
let struct_info_from_name loc n =
  try
    let { qualid = q;
          info = fields } = find_struct n in
    q, fields
  with
      Not_found -> message loc (Erecord_type_expected (Tid n))

(** @return the qualified name and list of fields of a record type.
    Prints an error message if the type is not a record type.
    [loc] is the location used for error reporting.*)
let struct_info loc ty = match ty with
  | Tid n -> struct_info_from_name loc n
  | _ -> message loc (Erecord_type_expected ty)

(** @return the qualified name and list of fields of the
    record type corresponding to the field named [n].
    Prints an error message if the type is not a record type.
    [loc] is the location used for error reporting.*)
let struct_info_from_field loc f =
  try
    let { qualid = q; info = n } = find_field f in
    struct_info_from_name loc (Modname { qual = q.qual; id = n })
  with
      Not_found -> message loc (Eundefined (fullname f))

(** [check_type t] checks that t exists *)
let rec check_type const_env = function
  | Tarray(ty, e) ->
      let typed_e = expect_static_exp const_env (Tid Initial.pint) e in
        Tarray(check_type const_env ty, typed_e)
  | Tid(ty_name) ->
      (try Tid(Modname((find_type ty_name).qualid))
       with Not_found -> error (Eundefined(fullname ty_name)))
  | Tprod l ->
      Tprod (List.map (check_type const_env) l)

and typing_static_exp const_env se =
  let desc, ty = match se.se_desc with
    | Sint v -> Sint v, Tid Initial.pint
    | Sbool v-> Sbool v, Tid Initial.pbool
    | Sfloat v -> Sfloat v, Tid Initial.pfloat
    | Svar ln ->
        (try (* this can be a global const*)
           let { qualid = q; info = cd } = find_const ln in
             Svar (Modname q), cd.Signature.c_type
         with Not_found -> (* or a static parameter *)
           (match ln with
              | Name n ->
                  (try Svar ln, NamesEnv.find n const_env
                  with Not_found -> message se.se_loc (Eundefined_const ln))
              | Modname _ -> message se.se_loc (Eundefined_const ln))
        )
    | Sconstructor c ->
        let { qualid = q; info = ty } = find_constr c in
          Sconstructor(Modname q), ty
    | Sop (op, se_list) ->
        let { qualid = q; info = ty_desc } = find_value op in
        let typed_se_list = typing_static_args const_env
          (types_of_arg_list ty_desc.node_inputs) se_list in
          Sop (Modname q, typed_se_list),
        prod (types_of_arg_list ty_desc.node_outputs)
    | Sarray_power (se, n) ->
        let typed_n = expect_static_exp const_env (Tid Initial.pint) n in
        let typed_se, ty = typing_static_exp const_env se in
          Sarray_power (typed_se, typed_n), Tarray(ty, n)
    | Sarray [] ->
        message se.se_loc Eempty_array
    | Sarray (se::se_list) ->
        let typed_se, ty = typing_static_exp const_env se in
        let typed_se_list = List.map (expect_static_exp const_env ty) se_list in
          Sarray (typed_se::typed_se_list),
        Tarray(ty, mk_static_exp (Sint ((List.length se_list) + 1)))
    | Stuple se_list ->
        let typed_se_list, ty_list = List.split
          (List.map (typing_static_exp const_env) se_list) in
        Stuple typed_se_list, prod ty_list
    | Srecord f_se_list ->
        (* find the record type using the first field *)
        let q, fields =
          (match f_se_list with
             | [] -> message se.se_loc (Eempty_record)
             | (f,_)::l -> struct_info_from_field se.se_loc f
          ) in

          if List.length f_se_list <> List.length fields then
            message se.se_loc Esome_fields_are_missing;
          check_static_field_unicity f_se_list;
          let f_se_list =
            List.map (typing_static_field const_env fields
                        (Tid (Modname q)) q.qual) f_se_list in
          Srecord f_se_list, Tid (Modname q)
  in
   { se with se_ty = ty; se_desc = desc }, ty

and typing_static_field const_env fields t1 modname (f,se) =
  try
    let ty = check_type const_env (field_assoc f fields) in
    let typed_se = expect_static_exp const_env ty se in
      Modname { qual = modname; id = shortname f }, typed_se
  with
      Not_found -> message se.se_loc (Eno_such_field (t1, f))

and typing_static_args const_env expected_ty_list e_list =
  try
    List.map2 (expect_static_exp const_env) expected_ty_list e_list
  with Invalid_argument _ ->
    error (Earity_clash(List.length e_list, List.length expected_ty_list))

and expect_static_exp const_env exp_ty se =
  let se, ty = typing_static_exp const_env se in
    try
      unify ty exp_ty; se
    with
      _ -> message se.se_loc (Etype_clash(ty, exp_ty))

(** @return the type of the field with name [f] in the list
    [fields]. [t1] is the corresponding record type and [loc] is
    the location, both used for error reporting. *)
let field_type const_env f fields t1 loc =
  try
    check_type const_env (field_assoc f fields)
  with
      Not_found -> message loc (Eno_such_field (t1, f))

let rec typing statefull const_env h e =
  try
    let typed_desc,ty = match e.e_desc with
      | Econst c ->
          let typed_c, ty = typing_static_exp const_env c in
            Econst typed_c, ty
      | Evar x ->
          Evar x, typ_of_varname h x
      | Elast x ->
          Elast x, typ_of_last h x

      | Eapp(op, e_list, r) ->
          let ty, op, typed_e_list =
            typing_app statefull const_env h op e_list in
            Eapp(op, typed_e_list, r), ty

      | Estruct(l) ->
          (* find the record type using the first field *)
          let q, fields =
            (match l with
               | [] -> message e.e_loc (Eempty_record)
               | (f,_)::l -> struct_info_from_field e.e_loc f
            ) in

          if List.length l <> List.length fields then
            message e.e_loc Esome_fields_are_missing;
          check_field_unicity l;
          let l =
            List.map (typing_field statefull
                        const_env h fields (Tid (Modname q)) q.qual) l in
          Estruct l, Tid (Modname q)

      | Epre (None, e) ->
          less_than statefull;
          let typed_e,ty = typing statefull const_env h e in
            Epre (None, typed_e), ty

      | Epre (Some c, e) ->
          less_than statefull;
          let typed_c, t1 = typing_static_exp const_env c in
          let typed_e = expect statefull const_env h t1 e in
            Epre(Some typed_c, typed_e), t1

      | Efby (e1, e2) ->
          less_than statefull;
          let typed_e1, t1 = typing statefull const_env h e1 in
          let typed_e2 = expect statefull const_env h t1 e2 in
            Efby (typed_e1, typed_e2), t1

      | Eiterator (it, ({ a_op = (Enode f | Efun f);
                          a_params = params } as app),
                   n, e_list, reset) ->
          let { qualid = q; info = ty_desc } = find_value f in
          let op, expected_ty_list, result_ty_list =
            kind (Modname q) statefull ty_desc in
          let m = build_subst ty_desc.node_params params in
          let expected_ty_list =
            List.map (subst_type_vars m) expected_ty_list in
          let result_ty_list = List.map (subst_type_vars m) result_ty_list in
          let typed_n = expect_static_exp const_env (Tid Initial.pint) n in
          let ty, typed_e_list = typing_iterator statefull const_env h it n
            expected_ty_list result_ty_list e_list in
          let typed_params = typing_node_params const_env
            ty_desc.node_params params in
            (* add size constraints *)
          let size_constrs =
            instanciate_constr m ty_desc.node_params_constraints in
            add_size_constraint (Clequal (mk_static_exp (Sint  1), typed_n));
            List.iter add_size_constraint size_constrs;
            (* return the type *)
            Eiterator(it, { app with a_op = op; a_params = typed_params }
                        , typed_n, typed_e_list, reset), ty
    in
      { e with e_desc = typed_desc; e_ty = ty; }, ty
  with
      TypingError(kind) -> message e.e_loc kind

and typing_field statefull const_env h fields t1 modname (f, e) =
  try
    let ty = check_type const_env (field_assoc f fields) in
    let typed_e = expect statefull const_env h ty e in
    Modname { qual = modname; id = shortname f }, typed_e
  with
      Not_found -> message e.e_loc (Eno_such_field (t1, f))

and expect statefull const_env h expected_ty e =
  let typed_e, actual_ty = typing statefull const_env h e in
  try
    unify actual_ty expected_ty;
    typed_e
  with TypingError(kind) -> message e.e_loc kind

and typing_app statefull const_env h op e_list =
  match op, e_list with
    | { a_op = Earrow }, [e1;e2] ->
        less_than statefull;
        let typed_e1, t1 = typing statefull const_env h e1 in
        let typed_e2 = expect statefull const_env h t1 e2 in
        t1, op, [typed_e1;typed_e2]

    | { a_op = Eifthenelse }, [e1;e2;e3] ->
        let typed_e1 = expect statefull const_env h
          (Tid Initial.pbool) e1 in
        let typed_e2, t1 = typing statefull const_env h e2 in
        let typed_e3 = expect statefull const_env h t1 e3 in
        t1, op, [typed_e1; typed_e2; typed_e3]

    | { a_op = (Efun f | Enode f); a_params = params } as app, e_list ->
        let { qualid = q; info = ty_desc } = find_value f in
        let op, expected_ty_list, result_ty_list =
          kind (Modname q) statefull ty_desc in
        let m = build_subst ty_desc.node_params params in
        let expected_ty_list = List.map (subst_type_vars m) expected_ty_list in
        let typed_e_list = typing_args statefull const_env h
          expected_ty_list e_list in
        let result_ty_list = List.map (subst_type_vars m) result_ty_list in
        (* Type static parameters and generate constraints *)
        let typed_params = typing_node_params const_env
          ty_desc.node_params params in
        let size_constrs =
          instanciate_constr m ty_desc.node_params_constraints in
        List.iter add_size_constraint size_constrs;
        prod result_ty_list,
        { app with a_op = op; a_params = typed_params },
         typed_e_list

    | { a_op = Etuple }, e_list ->
        let typed_e_list,ty_list =
          List.split (List.map (typing statefull const_env h) e_list) in
         prod ty_list, op, typed_e_list

    | { a_op = Earray }, exp::e_list ->
        let typed_exp, t1 = typing statefull const_env h exp in
        let typed_e_list = List.map (expect statefull const_env h t1) e_list in
        let n = mk_static_exp ~ty:(Tid Initial.pint)
          (Sint (List.length e_list + 1)) in
          Tarray(t1, n), op, typed_exp::typed_e_list

    | { a_op = Efield; a_params = [f] }, [e] ->
        let fn =
          (match f.se_desc with
             | Sconstructor fn -> fn
             | _ -> assert false) in
        let typed_e, t1 = typing statefull const_env h e in
        let q, fields = struct_info e.e_loc t1 in
        let t2 = field_type const_env fn fields t1 e.e_loc in
        let fn = Modname { qual = q.qual; id = shortname fn } in
        let f = { f with se_desc = Sconstructor fn } in
          t2, { op with a_params = [f] }, [typed_e]

    | { a_op = Efield_update; a_params = [f] }, [e1; e2] ->
        let typed_e1, t1 = typing statefull const_env h e1 in
        let q, fields = struct_info e1.e_loc t1 in
        let fn =
          (match f.se_desc with
             | Sconstructor fn -> fn
             | _ -> assert false) in
        let f = { f with se_desc =
            Sconstructor (Modname { qual = q.qual; id = shortname fn }) } in
        let t2 = field_type const_env fn fields t1 e1.e_loc in
        let typed_e2 = expect statefull const_env h t2 e2 in
        t1, { op with a_params = [f] } , [typed_e1; typed_e2]

    | { a_op = Earray_fill; a_params = [n] }, [e1] ->
        let typed_n = expect_static_exp const_env (Tid Initial.pint) n in
        let typed_e1, t1 = typing statefull const_env h e1 in
          add_size_constraint (Clequal (mk_static_exp (Sint 1), typed_n));
          Tarray (t1, typed_n), { op with a_params = [typed_n] }, [typed_e1]

    | { a_op = Eselect; a_params = idx_list }, [e1] ->
        let typed_e1, t1 = typing statefull const_env h e1 in
        let typed_idx_list, ty =
          typing_array_subscript statefull const_env h idx_list t1 in
          ty, { op with a_params = typed_idx_list }, [typed_e1]

    | { a_op = Eselect_dyn }, e1::defe::idx_list ->
        let typed_e1, t1 = typing statefull const_env h e1 in
        let typed_defe = expect statefull const_env h (element_type t1) defe in
        let ty, typed_idx_list =
          typing_array_subscript_dyn statefull const_env h idx_list t1 in
        ty, op, typed_e1::typed_defe::typed_idx_list

    | { a_op = Eupdate; a_params = idx_list }, [e1;e2] ->
        let typed_e1, t1 = typing statefull const_env h e1 in
        let typed_idx_list, ty =
          typing_array_subscript statefull const_env h idx_list t1 in
        let typed_e2 = expect statefull const_env h ty e2 in
          t1, { op with a_params = typed_idx_list }, [typed_e1; typed_e2]

    | { a_op = Eselect_slice; a_params = [idx1; idx2] }, [e] ->
        let typed_idx1 = expect_static_exp const_env (Tid Initial.pint) idx1 in
        let typed_idx2 = expect_static_exp const_env (Tid Initial.pint) idx2 in
        let typed_e, t1 = typing statefull const_env h e in
        (*Create the expression to compute the size of the array *)
        let e1 = mk_static_exp (Sop (mk_pervasives "-",
                                     [typed_idx2; typed_idx1])) in
        let e2 = mk_static_exp (Sop (mk_pervasives "+",
                                     [e1;mk_static_exp (Sint  1) ])) in
        add_size_constraint (Clequal (mk_static_exp (Sint  1), e2));
        Tarray (element_type t1, e2),
        { op with a_params = [typed_idx1; typed_idx2] }, [typed_e]

    | { a_op = Econcat }, [e1; e2] ->
        let typed_e1, t1 = typing statefull const_env h e1 in
        let typed_e2, t2 = typing statefull const_env h e2 in
        begin try
          unify (element_type t1) (element_type t2)
        with
            TypingError(kind) -> message e1.e_loc kind
        end;
        let n = mk_static_exp (Sop (mk_pervasives "+",
                                    [array_size t1; array_size t2])) in
        Tarray (element_type t1, n), op, [typed_e1; typed_e2]

    (*Arity problems*)
    | { a_op = Earrow }, _ ->
        error (Earity_clash(List.length e_list, 2))
    | { a_op = Eifthenelse }, _ ->
        error (Earity_clash(List.length e_list, 2))
    | { a_op = Efield_update }, _ ->
        error (Earity_clash(List.length e_list, 2))
    | { a_op = Earray }, [] ->
        error (Earity_clash (0, 1))
    | { a_op = Econcat }, _ ->
        error (Earity_clash(List.length e_list, 2))
    | { a_op = Eselect_slice }, _ ->
        error (Earity_clash(List.length e_list, 3))
    | { a_op = Eupdate }, _ ->
        error (Earity_clash(List.length e_list, 2))
    | { a_op = Eselect }, _ ->
        error (Earity_clash(List.length e_list, 1))
    | { a_op = Eselect_dyn }, _ ->
        error (Earity_clash(List.length e_list, 2))
    | { a_op = Earray_fill }, _ ->
        error (Earity_clash(List.length e_list, 2))

and typing_iterator statefull const_env h
    it n args_ty_list result_ty_list e_list = match it with
  | Imap ->
      let args_ty_list = List.map (fun ty -> Tarray(ty, n)) args_ty_list in
      let result_ty_list =
        List.map (fun ty -> Tarray(ty, n)) result_ty_list in
      let typed_e_list = typing_args statefull const_env h
        args_ty_list e_list in
      prod result_ty_list, typed_e_list

  | Ifold ->
      let args_ty_list =
        incomplete_map (fun ty -> Tarray (ty, n)) args_ty_list in
      let typed_e_list =
        typing_args statefull const_env h args_ty_list e_list in
      (*check accumulator type matches in input and output*)
      if List.length result_ty_list > 1 then error Etoo_many_outputs;
      ( try unify (last_element args_ty_list) (List.hd result_ty_list)
        with TypingError(kind) -> message (List.hd e_list).e_loc kind );
      (List.hd result_ty_list), typed_e_list

    | Imapfold ->
      let args_ty_list =
        incomplete_map (fun ty -> Tarray (ty, n)) args_ty_list in
      let result_ty_list =
        incomplete_map (fun ty -> Tarray (ty, n)) result_ty_list in
      let typed_e_list = typing_args statefull const_env h
        args_ty_list e_list in
      (*check accumulator type matches in input and output*)
      ( try unify (last_element args_ty_list) (last_element result_ty_list)
        with TypingError(kind) -> message (List.hd e_list).e_loc kind );
      prod result_ty_list, typed_e_list

and typing_array_subscript statefull const_env h idx_list ty  =
  match ty, idx_list with
    | ty, [] -> [], ty
    | Tarray(ty, exp), idx::idx_list ->
        ignore (expect_static_exp const_env (Tid Initial.pint) exp);
        let typed_idx = expect_static_exp const_env (Tid Initial.pint) idx in
        add_size_constraint (Clequal (mk_static_exp (Sint 0), idx));
        let bound =  mk_static_exp (Sop(mk_pervasives "-",
                                        [exp; mk_static_exp (Sint 1)])) in
          add_size_constraint (Clequal (idx,bound));
          let typed_idx_list, ty =
            typing_array_subscript statefull const_env h idx_list ty in
          typed_idx::typed_idx_list, ty
    | _, _ -> error (Esubscripted_value_not_an_array ty)

(* This function checks that the array dimensions matches
   the subscript. It returns the base type wrt the nb of indices. *)
and typing_array_subscript_dyn statefull const_env h idx_list ty =
  match ty, idx_list with
    | ty, [] -> ty, []
    | Tarray(ty, exp), idx::idx_list ->
        let typed_idx = expect statefull const_env h (Tid Initial.pint) idx in
        let ty, typed_idx_list =
          typing_array_subscript_dyn statefull const_env h idx_list ty in
        ty, typed_idx::typed_idx_list
    | _, _ -> error (Esubscripted_value_not_an_array ty)

and typing_args statefull const_env h expected_ty_list e_list =
  try
    List.map2 (expect statefull const_env h) expected_ty_list e_list
  with Invalid_argument _ ->
    error (Earity_clash(List.length e_list, List.length expected_ty_list))

and typing_node_params const_env params_sig params =
  List.map2 (fun p_sig p -> expect_static_exp const_env
               p_sig.p_type p) params_sig params

let rec typing_pat h acc = function
  | Evarpat(x) ->
      let ty = typ_of_name h x in
      let acc =
        if Env.mem x acc
        then error (Ealready_defined (sourcename x))
        else Env.add x ty acc in
      acc, ty
  | Etuplepat(pat_list) ->
      let acc, ty_list =
        List.fold_right
          (fun pat (acc, ty_list) ->
             let acc, ty = typing_pat h acc pat in acc, ty :: ty_list)
          pat_list (acc, []) in
      acc, Tprod(ty_list)

let rec typing_eq statefull const_env h acc eq =
  let typed_desc,acc = match eq.eq_desc with
    | Eautomaton(state_handlers) ->
        let typed_sh,acc =
          typing_automaton_handlers statefull const_env h acc state_handlers in
        Eautomaton(typed_sh),
        acc
    | Eswitch(e, switch_handlers) ->
        let typed_e,ty = typing statefull const_env h e in
        let typed_sh,acc =
          typing_switch_handlers statefull const_env h acc ty switch_handlers in
        Eswitch(typed_e,typed_sh),
        acc
    | Epresent(present_handlers, b) ->
        let typed_b, def_names, _ = typing_block statefull const_env h b in
        let typed_ph, acc =
          typing_present_handlers statefull const_env h
            acc def_names present_handlers in
        Epresent(typed_ph,typed_b),
        acc
    | Ereset(eq_list, e) ->
        let typed_e = expect statefull const_env h (Tid Initial.pbool) e in
        let typed_eq_list, acc = typing_eq_list statefull
          const_env h acc eq_list in
        Ereset(typed_eq_list,typed_e),
        acc
    | Eeq(pat, e) ->
        let acc, ty_pat = typing_pat h acc pat in
        let typed_e = expect statefull const_env h ty_pat e in
        Eeq(pat, typed_e),
        acc in
  { eq with
      eq_statefull = is_statefull_eq_desc typed_desc;
      eq_desc = typed_desc },
  acc

and typing_eq_list statefull const_env h acc eq_list =
  let rev_typed_eq_list,acc =
    List.fold_left
      (fun (rev_eq_list,acc) eq ->
         let typed_eq, acc = typing_eq statefull const_env h acc eq in
         (typed_eq::rev_eq_list),acc
      )
      ([],acc)
      eq_list in
  ((List.rev rev_typed_eq_list),
   acc)

and typing_automaton_handlers statefull const_env h acc state_handlers =
  (* checks unicity of states *)
  let addname acc { s_state = n } =
    if S.mem n acc then error (Ealready_defined(n)) else S.add n acc in
  let states =  List.fold_left addname S.empty state_handlers in

  let escape statefull h ({ e_cond = e; e_next_state = n } as esc) =
    if not (S.mem n states) then error (Eundefined(n));
    let typed_e = expect statefull const_env h (Tid Initial.pbool) e in
    { esc with e_cond = typed_e } in

  let handler ({ s_state = n; s_block = b; s_until = e_list1;
                 s_unless = e_list2 } as s) =
    let typed_b, defined_names, h0 = typing_block statefull const_env h b in
    let typed_e_list1 = List.map (escape statefull h0) e_list1 in
    let typed_e_list2 = List.map (escape false h) e_list2 in
    { s with
        s_block = typed_b;
        s_until = typed_e_list1;
        s_unless = typed_e_list2 },
    defined_names in

  let typed_handlers,defined_names_list =
    List.split (List.map handler state_handlers) in
  let total, partial = merge defined_names_list in
  all_last h partial;
  typed_handlers,
      (add total (add partial acc))

and typing_switch_handlers statefull const_env h acc ty switch_handlers =
  (* checks unicity of states *)
  let addname acc { w_name = n } =
    let n = shortname(n) in
    if S.mem n acc then error (Ealready_defined(n)) else S.add n acc in
  let cases = List.fold_left addname S.empty switch_handlers in
  let d = diff_const (set_of_constr (desc_of_ty ty)) cases in
  if not (S.is_empty d) then error (Epartial_switch(S.choose d));

  let handler ({ w_block = b; w_name = name }) =
    let typed_b, defined_names, _ = typing_block statefull const_env h b in
    { w_block = typed_b;
      (* Replace handler name with fully qualified name *)
      w_name = Modname((find_constr name).qualid)},
    defined_names in

  let typed_switch_handlers, defined_names_list =
    List.split (List.map handler switch_handlers) in
  let total, partial = merge defined_names_list in
  all_last h partial;
  (typed_switch_handlers,
   add total (add partial acc))

and typing_present_handlers statefull const_env h acc def_names
    present_handlers =
  let handler ({ p_cond = e; p_block = b }) =
    let typed_e = expect false const_env h (Tid Initial.pbool) e in
    let typed_b, defined_names, _ = typing_block statefull const_env h b in
    { p_cond = typed_e; p_block = typed_b },
    defined_names
  in

  let typed_present_handlers, defined_names_list =
    List.split (List.map handler present_handlers) in
  let total, partial = merge (def_names :: defined_names_list) in
  all_last h partial;
  (typed_present_handlers,
   (add total (add partial acc)))

and typing_block statefull const_env h
    ({ b_local = l; b_equs = eq_list; b_loc = loc } as b) =
  try
    let typed_l, local_names, h0 = build const_env h Env.empty l in
    let typed_eq_list, defined_names =
      typing_eq_list statefull const_env h0 Env.empty eq_list in
    let defnames = diff_env defined_names local_names in
    { b with
        b_statefull = List.exists (fun eq -> eq.eq_statefull) typed_eq_list;
        b_defnames = defnames;
        b_local = typed_l;
        b_equs = typed_eq_list },
    defnames, h0
  with
    | TypingError(kind) -> message loc kind

and build const_env h h0 dec =
  List.fold_left
    (fun (acc_dec, acc_defined, h)
       ({ v_ident = n; v_type = btype; v_last = l; v_loc = loc } as v) ->
         try
           let ty = check_type const_env btype in
           (* update type longname with module name from check_type *)
           v.v_type <- ty;
           if (Env.mem n h0) or (Env.mem n h)
           then error (Ealready_defined(sourcename n))
           else
             ({ v with v_type = ty }::acc_dec,
              Env.add n ty acc_defined,
              Env.add n { ty = ty; last = last l } h)
         with
           | TypingError(kind) -> message loc kind)
    ([], Env.empty, h) dec

let typing_contract statefull const_env h contract =

  match contract with
    | None -> None,h
    | Some ({ c_local = l_list;
              c_eq = eq;
              c_assume = e_a;
              c_enforce = e_g }) ->
        let typed_l_list, local_names, h' = build const_env h h l_list in

        let typed_eq, defined_names =
          typing_eq_list statefull const_env h' Env.empty eq in

        (* assumption *)
        let typed_e_a = expect statefull const_env h' (Tid Initial.pbool) e_a in
        (* property *)
        let typed_e_g = expect statefull const_env h' (Tid Initial.pbool) e_g in

        included_env local_names defined_names;
        included_env defined_names local_names;

        Some { c_local = typed_l_list;
               c_eq = typed_eq;
               c_assume = typed_e_a;
               c_enforce = typed_e_g }, h

let signature statefull inputs returns params constraints =
  let arg_dec_of_var_dec vd =
    mk_arg (Some (name vd.v_ident)) (simplify_type vd.v_loc vd.v_type)
  in
  { node_inputs = List.map arg_dec_of_var_dec inputs;
    node_outputs = List.map arg_dec_of_var_dec returns;
    node_statefull = statefull;
    node_params = params;
    node_params_constraints = constraints; }

let solve loc cl =
  try
    solve NamesEnv.empty cl
  with
      Solve_failed c -> message loc (Econstraint_solve_failed c)

let build_node_params const_env l =
  let check_param env p =
    let ty = check_type const_env p.p_type in
      { p with p_type = ty }, NamesEnv.add p.p_name ty env
  in
    mapfold check_param const_env l

let node ({ n_name = f; n_statefull = statefull;
            n_input = i_list; n_output = o_list;
            n_contract = contract;
            n_local = l_list; n_equs = eq_list; n_loc = loc;
            n_params = node_params; } as n) =
  try
    let typed_params, const_env =
      build_node_params NamesEnv.empty node_params in
    let typed_i_list, input_names, h =
      build const_env Env.empty Env.empty i_list in
    let typed_i_list = List.rev typed_i_list in
    let typed_o_list, output_names, h = build const_env h h o_list in
    let typed_o_list = List.rev typed_o_list in

    (* typing contract *)
    let typed_contract, h =
      typing_contract statefull const_env h contract in

    let typed_l_list, local_names, h = build const_env h h l_list in
    let typed_eq_list, defined_names =
      typing_eq_list statefull const_env h Env.empty eq_list in
    (* if not (statefull) & (List.length o_list <> 1)
       then error (Etoo_many_outputs);*)
    let expected_names = add local_names output_names in
    included_env expected_names defined_names;
    included_env defined_names expected_names;

    let cl = get_size_constraint () in
    let cl = solve loc cl in
    add_value f (signature statefull typed_i_list typed_o_list typed_params cl);

    { n with
        n_input = typed_i_list;
        n_output = typed_o_list;
        n_local = typed_l_list;
        n_params = typed_params;
        n_contract = typed_contract;
        n_equs = typed_eq_list }
  with
    | TypingError(error) -> message loc error

let deftype { t_name = n; t_desc = tdesc; t_loc = loc } =
  try
    match tdesc with
      | Type_abs -> add_type n Tabstract
      | Type_enum(tag_name_list) ->
          add_type n (Tenum tag_name_list);
          List.iter (fun tag -> add_constr tag (Tid (longname n))) tag_name_list
      | Type_struct(field_ty_list) ->
          let field_ty_list =
            List.map (fun f ->
                        mk_field f.f_name
                          (simplify_type loc
                             (check_type NamesEnv.empty f.f_type)))
              field_ty_list in
          add_type n (Tstruct field_ty_list);
          add_struct n field_ty_list;
          List.iter
            (fun f -> add_field f.f_name n) field_ty_list
  with
      TypingError(error) -> message loc error

let typing_const_dec cd =
  let ty = check_type NamesEnv.empty cd.c_type in
  let se = expect_static_exp NamesEnv.empty ty cd.c_value in
  let cd = { cd with c_value = se; c_type = ty } in
    add_const cd.c_name (mk_const_def cd.c_name cd.c_type cd.c_value);
    cd

let program
    ({ p_opened = opened; p_types = p_type_list;
       p_nodes = p_node_list; p_consts = p_consts_list } as p) =
  let typed_cd_list = List.map typing_const_dec p_consts_list in
    List.iter open_module opened;
    List.iter deftype p_type_list;
    let typed_node_list = List.map node p_node_list in
      { p with p_nodes = typed_node_list; p_consts = typed_cd_list }
