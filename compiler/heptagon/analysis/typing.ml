(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* type checking *)

open Misc
open Names
open Idents
open Location
open Signature
open Modules
open Initial
open Static
open Types
open Global_printer
open Heptagon
open Hept_mapfold

type value = { ty: ty; mutable last: bool }

type error =
  | Emissing of name
  | Emissingcase of name
  | Eundefined of name
  | Elast_undefined of name
  | Etype_clash of ty * ty
  | Earity_clash of int * int
  | Estatic_arity_clash of int * int
  | Ealready_defined of name
  | Enon_exaustive
  | Epartial_switch of name
  | Etoo_many_outputs
  | Esome_fields_are_missing
  | Esubscripted_value_not_an_array of ty
  | Earray_subscript_should_be_const
  | Eundefined_const of qualname
  | Econstraint_solve_failed of size_constraint
  | Etype_should_be_static of ty
  | Erecord_type_expected of ty
  | Eno_such_field of ty * qualname
  | Eempty_record
  | Eempty_array
  | Efoldi_bad_args of ty

exception Unify
exception TypingError of error

let error kind = raise (TypingError(kind))

let message loc kind =
  begin match kind with
    | Emissing(s) ->
        Format.eprintf "%aNo equation is given for name %s.@."
          print_location loc
          s;
    | Emissingcase(s) ->
        Format.eprintf "%aCase %s not defined.@."
          print_location loc
          s;
    | Eundefined(s) ->
        Format.eprintf "%aThe name %s is unbound.@."
          print_location loc
          s;
    | Elast_undefined(s) ->
        Format.eprintf "%aThe name %s does not have a last value.@."
          print_location loc
          s;
    | Etype_clash(actual_ty, expected_ty) ->
        Format.eprintf "%aType Clash: this expression has type %a, @\n\
            but is expected to have type %a.@."
          print_location loc
          print_type actual_ty
          print_type expected_ty
    | Earity_clash(actual_arit, expected_arit) ->
        Format.eprintf "%aType Clash: this expression expects %d arguments,@\n\
            but is expected to have %d.@."
          print_location loc
          expected_arit actual_arit
    | Estatic_arity_clash(actual_arit, expected_arit) ->
        Format.eprintf
          "%aType Clash: this node expects %d static parameters,@\n\
           but was given %d.@."
          print_location loc
          expected_arit actual_arit
    | Ealready_defined(s) ->
        Format.eprintf "%aThe name %s is already defined.@."
          print_location loc
          s
    | Enon_exaustive ->
        Format.eprintf "%aSome constructors are missing in this \
                        pattern/matching.@."
          print_location loc
    | Epartial_switch(s) ->
        Format.eprintf
          "%aThe case %s is missing.@."
          print_location loc
          s
    | Etoo_many_outputs ->
        Format.eprintf
          "%aA function may only returns a basic value.@."
          print_location loc
    | Esome_fields_are_missing ->
        Format.eprintf
          "%aSome fields are missing.@."
          print_location loc
    | Esubscripted_value_not_an_array  ty ->
        Format.eprintf
          "%aSubscript used on a non array type : %a.@."
          print_location loc
          Global_printer.print_type ty
    | Earray_subscript_should_be_const ->
        Format.eprintf
          "%aSubscript has to be a static value.@."
          print_location loc
    | Eundefined_const ln ->
        Format.eprintf
          "%aThe const name '%s' is unbound.@."
          print_location loc
          (fullname ln)
    | Econstraint_solve_failed c ->
        Format.eprintf
          "%aThe following constraint cannot be satisified:@\n%a.@."
          print_location loc
          print_size_constraint c
    | Etype_should_be_static ty ->
        Format.eprintf
          "%aThis type should be static : %a.@."
          print_location loc
          print_type ty
    | Erecord_type_expected ty ->
        Format.eprintf
          "%aA record was expected (found %a).@."
          print_location loc
          print_type ty
    | Eno_such_field (ty, f) ->
        Format.eprintf
          "%aThe record type '%a' does not have a '%s' field.@."
          print_location loc
          print_type ty
          (shortname f)
    | Eempty_record ->
        Format.eprintf
          "%aThe record is empty.@."
          print_location loc
    | Eempty_array ->
        Format.eprintf
          "%aThe array is empty.@."
          print_location loc
    | Efoldi_bad_args  ty ->
        Format.eprintf
          "%aThe function given to foldi should expect an integer \
               as the last but one argument (found: %a).@."
          print_location loc
          print_type ty
  end;
  raise Error

(** Add wrappers around Modules function to raise errors
    and display the correct location. *)
let add_with_error add_fun f v =
  try add_fun f v
  with Already_defined -> error (Ealready_defined (fullname f))
let find_with_error find_fun f =
  try find_fun f
  with Not_found -> error (Eundefined(fullname f))

let add_value = add_with_error add_value
let add_type = add_with_error add_type
let add_constrs = add_with_error add_constrs
let add_field = add_with_error add_field
let add_const = add_with_error add_const

let find_value = find_with_error find_value
let find_constrs = find_with_error find_constrs
let find_field = find_with_error find_field

(** Constraints related functions *)
let (curr_size_constr : size_constraint list ref) = ref []
let add_size_constraint c =
  curr_size_constr := c::(!curr_size_constr)
let get_size_constraint () =
  let l = !curr_size_constr in
  curr_size_constr := [];
  l

(** Helper functions to work with types *)
let get_number_of_fields ty =
  let tydesc =
    match ty with
      | Tid(f) -> find_type f
      | _ -> assert false in
  match tydesc with
    | Tstruct l -> List.length l
    | _ -> assert false

let element_type ty =
  match unalias_type ty with
    | Tarray (ty, _) -> ty
    | _ -> error (Esubscripted_value_not_an_array ty)

let array_size ty =
  match unalias_type ty with
    | Tarray (_, e) -> e
    | _ -> error (Esubscripted_value_not_an_array ty)

let unalias_type ty =
  try unalias_type ty
  with Undefined_type ln -> error (Eundefined (fullname ln))

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
  let ut1 = unalias_type t1 in
  let ut2 = unalias_type t2 in
  try unify ut1 ut2 with Unify -> error (Etype_clash(t1, t2))

let kind f ty_desc =
  let ty_of_arg v = v.a_type in
  let op = if ty_desc.node_statefull then Enode f else Efun f in
    op, List.map ty_of_arg ty_desc.node_inputs,
  List.map ty_of_arg ty_desc.node_outputs

let typ_of_name h x =
  try
    let { ty = ty } = Env.find x h in ty
  with
      Not_found -> error (Eundefined(sourcename x))

let desc_of_ty = function
  | Tid n when n = pbool  -> Tenum [ptrue; pfalse]
  | Tid ty_name -> find_type ty_name
  | _  -> Tabstract
let set_of_constr = function
  | Tabstract | Tstruct _  -> assert false
  | Tenum tag_list -> List.fold_right QualSet.add tag_list QualSet.empty

let name_mem n env =
  let check_one id _ acc =
    ((name id) = n) or acc
  in
  Env.fold check_one env false

(*let rec simplify_type = function
  | Tid _ as t -> t
  | Tarray(ty, e) ->
      Tarray(simplify_type ty, simplify NamesEnv.empty e)
  | Tprod l ->
      Tprod (List.map simplify_type l)

let simplify_type loc ty =
  try
    simplify_type ty
  with
      Instanciation_failed -> message loc (Etype_should_be_static ty) *)

let build_subst names values =
  if List.length names <> List.length values
  then error (Estatic_arity_clash (List.length values, List.length names));
  List.fold_left2 (fun m n v -> QualEnv.add n v m)
    QualEnv.empty names values

let rec subst_type_vars m = function
  | Tarray(ty, e) -> Tarray(subst_type_vars m ty, static_exp_subst m e)
  | Tprod l -> Tprod (List.map (subst_type_vars m) l)
  | t -> t

let equal expected_tag_list actual_tag_list =
  if not (List.for_all
            (fun tag -> List.mem tag actual_tag_list) expected_tag_list)
  then error Enon_exaustive

let add_distinct_env id ty env =
  if Env.mem id env then
    error (Ealready_defined(name id))
  else
    Env.add id ty env

let add_distinct_qualset n acc =
  if QualSet.mem n acc then
    error (Ealready_defined (fullname n))
  else
    QualSet.add n acc

let add_distinct_S n acc =
  if S.mem n acc then
    error (Ealready_defined n)
  else
    S.add n acc

(** Add two sets of names provided they are distinct *)
let add env1 env2 =
  Env.fold add_distinct_env env1 env2

(** Checks that constructors are included in constructor list from type
    def and returns the difference *)
let included_const s1 s2 =
  QualSet.iter
    (fun elt -> if not (QualSet.mem elt s2)
      then error (Emissingcase (fullname elt)))
    s1

let diff_const defined_names local_names =
  included_const local_names defined_names;
  QualSet.diff defined_names local_names

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
let struct_info_from_name n =
  try
    n, find_struct n
  with
      Not_found -> error (Erecord_type_expected (Tid n))

(** @return the qualified name and list of fields of a record type.
    Prints an error message if the type is not a record type.
    [loc] is the location used for error reporting.*)
let struct_info ty = match ty with
  | Tid n -> struct_info_from_name n
  | _ -> error (Erecord_type_expected ty)

(** @return the qualified name and list of fields of the
    record type corresponding to the field named [n].
    Prints an error message if the type is not a record type.
    [loc] is the location used for error reporting.*)
let struct_info_from_field f =
  try
    struct_info_from_name (find_field f)
  with
      Not_found -> error (Eundefined (fullname f))

(** [check_type t] checks that t exists *)
let rec check_type const_env = function
  | Tarray(ty, e) ->
      let typed_e = expect_static_exp const_env (Tid Initial.pint) e in
        Tarray(check_type const_env ty, typed_e)
  | Tid ty_name -> Tid ty_name
  | Tprod l ->
      Tprod (List.map (check_type const_env) l)

and typing_static_exp const_env se =
  try
  let desc, ty = match se.se_desc with
    | Sint v -> Sint v, Tid Initial.pint
    | Sbool v-> Sbool v, Tid Initial.pbool
    | Sfloat v -> Sfloat v, Tid Initial.pfloat
    | Svar ln ->
        (try (* this can be a global const*)
           let cd = Modules.find_const ln in
             Svar ln, cd.Signature.c_type
(* TODO verifier... *)
         with Not_found -> (* or a static parameter *)
           Svar ln, QualEnv.find ln const_env)
    | Sconstructor c ->
      Sconstructor c, Tid (find_constrs c)
    | Sop (op, se_list) ->
        let ty_desc = find_value op in
        let typed_se_list = typing_static_args const_env
          (types_of_arg_list ty_desc.node_inputs) se_list in
          Sop (op, typed_se_list),
        prod (types_of_arg_list ty_desc.node_outputs)
    | Sarray_power (se, n) ->
        let typed_n = expect_static_exp const_env (Tid Initial.pint) n in
        let typed_se, ty = typing_static_exp const_env se in
          Sarray_power (typed_se, typed_n), Tarray(ty, typed_n)
    | Sarray [] ->
        message se.se_loc Eempty_array
    | Sarray (se::se_list) ->
        let typed_se, ty = typing_static_exp const_env se in
        let typed_se_list = List.map (expect_static_exp const_env ty) se_list in
          Sarray (typed_se::typed_se_list),
        Tarray(ty, mk_static_int ((List.length se_list) + 1))
    | Stuple se_list ->
        let typed_se_list, ty_list = List.split
          (List.map (typing_static_exp const_env) se_list) in
        Stuple typed_se_list, prod ty_list
    | Srecord f_se_list ->
        (* find the record type using the first field *)
        let q, fields =
          (match f_se_list with
             | [] -> error (Eempty_record)
             | (f,_)::l -> struct_info_from_field f
          ) in

          if List.length f_se_list <> List.length fields then
            message se.se_loc Esome_fields_are_missing;
          check_static_field_unicity f_se_list;
          let f_se_list =
            List.map (typing_static_field const_env fields
                        (Tid q)) f_se_list in
          Srecord f_se_list, Tid q
  in
   { se with se_ty = ty; se_desc = desc }, ty

  with
      TypingError kind -> message se.se_loc kind

and typing_static_field const_env fields t1 (f,se) =
  try
    let ty = check_type const_env (field_assoc f fields) in
    let typed_se = expect_static_exp const_env ty se in
      f, typed_se
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

let rec typing const_env h e =
  try
    let typed_desc,ty = match e.e_desc with
      | Econst c ->
          let typed_c, ty = typing_static_exp const_env c in
            Econst typed_c, ty
      | Evar x ->
          Evar x, typ_of_name h x
      | Elast x ->
          Elast x, typ_of_name h x

      | Eapp(op, e_list, r) ->
          let ty, op, typed_e_list =
            typing_app const_env h op e_list in
            Eapp(op, typed_e_list, r), ty

      | Estruct(l) ->
          (* find the record type using the first field *)
          let q, fields =
            (match l with
               | [] -> message e.e_loc (Eempty_record)
               | (f,_)::l -> struct_info_from_field f
            ) in

          if List.length l <> List.length fields then
            message e.e_loc Esome_fields_are_missing;
          check_field_unicity l;
          let l =
            List.map (typing_field
                        const_env h fields (Tid q)) l in
          Estruct l, Tid q

      | Epre (None, e) ->
          let typed_e,ty = typing const_env h e in
            Epre (None, typed_e), ty

      | Epre (Some c, e) ->
          let typed_c, t1 = typing_static_exp const_env c in
          let typed_e = expect const_env h t1 e in
            Epre(Some typed_c, typed_e), t1

      | Efby (e1, e2) ->
          let typed_e1, t1 = typing const_env h e1 in
          let typed_e2 = expect const_env h t1 e2 in
            Efby (typed_e1, typed_e2), t1

      | Eiterator (it, ({ a_op = (Enode f | Efun f);
                          a_params = params } as app),
                   n, e_list, reset) ->
          let ty_desc = find_value f in
          let op, expected_ty_list, result_ty_list = kind f ty_desc in
(*TODO verifier....*)
          let node_params =
            List.map (fun { p_name = n } -> local_qn n) ty_desc.node_params in
          let m = build_subst node_params params in
          let expected_ty_list =
            List.map (subst_type_vars m) expected_ty_list in
          let result_ty_list = List.map (subst_type_vars m) result_ty_list in
          let typed_n = expect_static_exp const_env (Tid Initial.pint) n in
          let ty, typed_e_list = typing_iterator const_env h it n
            expected_ty_list result_ty_list e_list in
          let typed_params = typing_node_params const_env
            ty_desc.node_params params in
            (* add size constraints *)
          let size_constrs =
            instanciate_constr m ty_desc.node_params_constraints in
            add_size_constraint (Clequal (mk_static_int 1, typed_n));
            List.iter add_size_constraint size_constrs;
            (* return the type *)
            Eiterator(it, { app with a_op = op; a_params = typed_params }
                        , typed_n, typed_e_list, reset), ty
    in
      { e with e_desc = typed_desc; e_ty = ty; }, ty
  with
      TypingError(kind) -> message e.e_loc kind

and typing_field const_env h fields t1 (f, e) =
  try
    let ty = check_type const_env (field_assoc f fields) in
    let typed_e = expect const_env h ty e in
      f, typed_e
  with
      Not_found -> message e.e_loc (Eno_such_field (t1, f))

and expect const_env h expected_ty e =
  let typed_e, actual_ty = typing const_env h e in
  try
    unify actual_ty expected_ty;
    typed_e
  with TypingError(kind) -> message e.e_loc kind

and typing_app const_env h op e_list =
  match op, e_list with
    | { a_op = Eequal }, [e1;e2] ->
        let typed_e1, t1 = typing const_env h e1 in
        let typed_e2 = expect const_env h t1 e2 in
          Tid Initial.pbool, op, [typed_e1; typed_e2]

    | { a_op = Earrow }, [e1;e2] ->
        let typed_e1, t1 = typing const_env h e1 in
        let typed_e2 = expect const_env h t1 e2 in
        t1, op, [typed_e1;typed_e2]

    | { a_op = Eifthenelse }, [e1;e2;e3] ->
        let typed_e1 = expect const_env h
          (Tid Initial.pbool) e1 in
        let typed_e2, t1 = typing const_env h e2 in
        let typed_e3 = expect const_env h t1 e3 in
        t1, op, [typed_e1; typed_e2; typed_e3]

    | { a_op = (Efun f | Enode f); a_params = params } as app, e_list ->
        let ty_desc = find_value f in
        let op, expected_ty_list, result_ty_list = kind f ty_desc in
(*TODO verifier....*)
        let node_params =
          List.map (fun { p_name = n } -> local_qn n) ty_desc.node_params in
        let m = build_subst node_params params in
        let expected_ty_list = List.map (subst_type_vars m) expected_ty_list in
        let typed_e_list = typing_args const_env h
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
          List.split (List.map (typing const_env h) e_list) in
         prod ty_list, op, typed_e_list

    | { a_op = Earray }, exp::e_list ->
        let typed_exp, t1 = typing const_env h exp in
        let typed_e_list = List.map (expect const_env h t1) e_list in
        let n = mk_static_int (List.length e_list + 1) in
          Tarray(t1, n), op, typed_exp::typed_e_list

    | { a_op = Efield; a_params = [f] }, [e] ->
        let fn =
          (match f.se_desc with
             | Sconstructor fn -> fn
             | _ -> assert false) in
        let typed_e, t1 = typing const_env h e in
        let q, fields = struct_info t1 in
        let t2 = field_type const_env fn fields t1 e.e_loc in
          t2, op, [typed_e]

    | { a_op = Efield_update; a_params = [f] }, [e1; e2] ->
        let typed_e1, t1 = typing const_env h e1 in
        let q, fields = struct_info t1 in
        let fn =
          (match f.se_desc with
             | Sconstructor fn -> fn
             | _ -> assert false) in
        let t2 = field_type const_env fn fields t1 e1.e_loc in
        let typed_e2 = expect const_env h t2 e2 in
        t1, op, [typed_e1; typed_e2]

    | { a_op = Earray_fill; a_params = [n] }, [e1] ->
        let typed_n = expect_static_exp const_env (Tid Initial.pint) n in
        let typed_e1, t1 = typing const_env h e1 in
          add_size_constraint (Clequal (mk_static_int 1, typed_n));
          Tarray (t1, typed_n), { op with a_params = [typed_n] }, [typed_e1]

    | { a_op = Eselect; a_params = idx_list }, [e1] ->
        let typed_e1, t1 = typing const_env h e1 in
        let typed_idx_list, ty =
          typing_array_subscript const_env h idx_list t1 in
          ty, { op with a_params = typed_idx_list }, [typed_e1]

    | { a_op = Eselect_dyn }, e1::defe::idx_list ->
        let typed_e1, t1 = typing const_env h e1 in
        let typed_defe = expect const_env h (element_type t1) defe in
        let ty, typed_idx_list =
          typing_array_subscript_dyn const_env h idx_list t1 in
        ty, op, typed_e1::typed_defe::typed_idx_list

    | { a_op = Eupdate }, e1::e2::idx_list ->
        let typed_e1, t1 = typing const_env h e1 in
        let ty, typed_idx_list =
          typing_array_subscript_dyn const_env h idx_list t1 in
        let typed_e2 = expect const_env h ty e2 in
          t1, op, typed_e1::typed_e2::typed_idx_list

    | { a_op = Eselect_slice; a_params = [idx1; idx2] }, [e] ->
        let typed_idx1 = expect_static_exp const_env (Tid Initial.pint) idx1 in
        let typed_idx2 = expect_static_exp const_env (Tid Initial.pint) idx2 in
        let typed_e, t1 = typing const_env h e in
        (*Create the expression to compute the size of the array *)
        let e1 =
          mk_static_int_op (mk_pervasives "-") [typed_idx2; typed_idx1] in
        let e2 =
          mk_static_int_op (mk_pervasives "+") [e1;mk_static_int 1 ] in
        add_size_constraint (Clequal (mk_static_int 1, e2));
        Tarray (element_type t1, e2),
        { op with a_params = [typed_idx1; typed_idx2] }, [typed_e]

    | { a_op = Econcat }, [e1; e2] ->
        let typed_e1, t1 = typing const_env h e1 in
        let typed_e2, t2 = typing const_env h e2 in
        begin try
          unify (element_type t1) (element_type t2)
        with
            TypingError(kind) -> message e1.e_loc kind
        end;
        let n =
          mk_static_int_op (mk_pervasives "+") [array_size t1; array_size t2] in
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

and typing_iterator const_env h
    it n args_ty_list result_ty_list e_list = match it with
  | Imap ->
      let args_ty_list = List.map (fun ty -> Tarray(ty, n)) args_ty_list in
      let result_ty_list =
        List.map (fun ty -> Tarray(ty, n)) result_ty_list in
      let typed_e_list = typing_args const_env h
        args_ty_list e_list in
      prod result_ty_list, typed_e_list

  | Ifold ->
      let args_ty_list =
        incomplete_map (fun ty -> Tarray (ty, n)) args_ty_list in
      let typed_e_list =
        typing_args const_env h args_ty_list e_list in
      (*check accumulator type matches in input and output*)
      if List.length result_ty_list > 1 then error Etoo_many_outputs;
      ( try unify (last_element args_ty_list) (List.hd result_ty_list)
        with TypingError(kind) -> message (List.hd e_list).e_loc kind );
      (List.hd result_ty_list), typed_e_list

  | Ifoldi ->
      let args_ty_list, acc_ty = split_last args_ty_list in
      let args_ty_list, idx_ty = split_last args_ty_list in
        (* Last but one arg of the function should be integer *)
        ( try unify idx_ty (Tid Initial.pint)
          with TypingError _ -> raise (TypingError (Efoldi_bad_args idx_ty)));
        let args_ty_list =
        incomplete_map (fun ty -> Tarray (ty, n)) (args_ty_list@[acc_ty]) in
      let typed_e_list =
        typing_args const_env h args_ty_list e_list in
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
      let typed_e_list = typing_args const_env h
        args_ty_list e_list in
      (*check accumulator type matches in input and output*)
      ( try unify (last_element args_ty_list) (last_element result_ty_list)
        with TypingError(kind) -> message (List.hd e_list).e_loc kind );
      prod result_ty_list, typed_e_list

and typing_array_subscript const_env h idx_list ty  =
  match unalias_type ty, idx_list with
    | ty, [] -> [], ty
    | Tarray(ty, exp), idx::idx_list ->
        ignore (expect_static_exp const_env (Tid Initial.pint) exp);
        let typed_idx = expect_static_exp const_env (Tid Initial.pint) idx in
        add_size_constraint (Clequal (mk_static_int 0, idx));
        let bound =
          mk_static_int_op (mk_pervasives "-") [exp; mk_static_int 1] in
        add_size_constraint (Clequal (idx,bound));
        let typed_idx_list, ty =
          typing_array_subscript const_env h idx_list ty in
        typed_idx::typed_idx_list, ty
    | _, _ -> error (Esubscripted_value_not_an_array ty)

(* This function checks that the array dimensions matches
   the subscript. It returns the base type wrt the nb of indices. *)
and typing_array_subscript_dyn const_env h idx_list ty =
  match unalias_type ty, idx_list with
    | ty, [] -> ty, []
    | Tarray(ty, exp), idx::idx_list ->
        let typed_idx = expect const_env h (Tid Initial.pint) idx in
        let ty, typed_idx_list =
          typing_array_subscript_dyn const_env h idx_list ty in
        ty, typed_idx::typed_idx_list
    | _, _ -> error (Esubscripted_value_not_an_array ty)

and typing_args const_env h expected_ty_list e_list =
  try
    List.map2 (expect const_env h) expected_ty_list e_list
  with Invalid_argument _ ->
    error (Earity_clash(List.length e_list, List.length expected_ty_list))

and typing_node_params const_env params_sig params =
  List.map2 (fun p_sig p -> expect_static_exp const_env
               p_sig.p_type p) params_sig params

let rec typing_pat h acc = function
  | Evarpat(x) ->
      let ty = typ_of_name h x in
      let acc = add_distinct_env x ty acc in
      acc, ty
  | Etuplepat(pat_list) ->
      let acc, ty_list =
        List.fold_right
          (fun pat (acc, ty_list) ->
             let acc, ty = typing_pat h acc pat in acc, ty :: ty_list)
          pat_list (acc, []) in
      acc, Tprod(ty_list)

let rec typing_eq const_env h acc eq =
  let typed_desc,acc = match eq.eq_desc with
    | Eautomaton(state_handlers) ->
        let typed_sh,acc =
          typing_automaton_handlers const_env h acc state_handlers in
        Eautomaton(typed_sh),
        acc
    | Eswitch(e, switch_handlers) ->
        let typed_e,ty = typing const_env h e in
        let typed_sh,acc =
          typing_switch_handlers const_env h acc ty switch_handlers in
        Eswitch(typed_e,typed_sh),
        acc
    | Epresent(present_handlers, b) ->
        let typed_b, def_names, _ = typing_block const_env h b in
        let typed_ph, acc =
          typing_present_handlers const_env h
            acc def_names present_handlers in
        Epresent(typed_ph,typed_b),
        acc
    | Ereset(b, e) ->
        let typed_e = expect const_env h (Tid Initial.pbool) e in
        let typed_eq_list, acc = typing_eq_list
          const_env h acc b.b_equs in
        let typed_b = { b with b_equs = typed_eq_list } in
        Ereset(typed_b, typed_e),
        acc
    | Eeq(pat, e) ->
        let acc, ty_pat = typing_pat h acc pat in
        let typed_e = expect const_env h ty_pat e in
        Eeq(pat, typed_e),
        acc in
  { eq with eq_desc = typed_desc }, acc

and typing_eq_list const_env h acc eq_list =
  mapfold (typing_eq const_env h) acc eq_list

and typing_automaton_handlers const_env h acc state_handlers =
  (* checks unicity of states *)
  let addname acc { s_state = n } =
    add_distinct_S n acc in
  let states =  List.fold_left addname S.empty state_handlers in

  let escape h ({ e_cond = e; e_next_state = n } as esc) =
    if not (S.mem n states) then error (Eundefined(n));
    let typed_e = expect const_env h (Tid Initial.pbool) e in
    { esc with e_cond = typed_e } in

  let handler ({ s_state = n; s_block = b; s_until = e_list1;
                 s_unless = e_list2 } as s) =
    let typed_b, defined_names, h0 = typing_block const_env h b in
    let typed_e_list1 = List.map (escape h0) e_list1 in
    let typed_e_list2 = List.map (escape h) e_list2 in
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

and typing_switch_handlers const_env h acc ty switch_handlers =
  (* checks unicity of states *)
  let addname acc { w_name = n } = add_distinct_qualset n acc in
  let cases = List.fold_left addname QualSet.empty switch_handlers in
  let d = diff_const (set_of_constr (desc_of_ty ty)) cases in
  if not (QualSet.is_empty d) then
    error (Epartial_switch (fullname (QualSet.choose d)));

  let handler ({ w_block = b } as sh) =
    let typed_b, defined_names, _ = typing_block const_env h b in
    { sh with w_block = typed_b }, defined_names in

  let typed_switch_handlers, defined_names_list =
    List.split (List.map handler switch_handlers) in
  let total, partial = merge defined_names_list in
  all_last h partial;
  (typed_switch_handlers,
   add total (add partial acc))

and typing_present_handlers const_env h acc def_names
    present_handlers =
  let handler ({ p_cond = e; p_block = b }) =
    let typed_e = expect const_env h (Tid Initial.pbool) e in
    let typed_b, defined_names, _ = typing_block const_env h b in
    { p_cond = typed_e; p_block = typed_b },
    defined_names
  in

  let typed_present_handlers, defined_names_list =
    List.split (List.map handler present_handlers) in
  let total, partial = merge (def_names :: defined_names_list) in
  all_last h partial;
  (typed_present_handlers,
   (add total (add partial acc)))

and typing_block const_env h
    ({ b_local = l; b_equs = eq_list; b_loc = loc } as b) =
  try
    let typed_l, (local_names, h0) = build const_env h l in
    let typed_eq_list, defined_names =
      typing_eq_list const_env h0 Env.empty eq_list in
    let defnames = diff_env defined_names local_names in
    { b with
        b_defnames = defnames;
        b_local = typed_l;
        b_equs = typed_eq_list },
    defnames, h0
  with
    | TypingError(kind) -> message loc kind

(** Builds environments from a var_dec list.
    [h] is the environment to start from.
    @return the typed list of var_dec, an environment mapping
    names to their types (aka defined names) and the environment
    mapping names to types and last that will be used for typing (aka h).*)
and build const_env h dec =
  let var_dec (acc_defined, h) vd =
    try
      let ty = check_type const_env vd.v_type in

      let last_dec = match vd.v_last with
        | Last (Some se) -> Last (Some (expect_static_exp const_env ty se))
        | Var | Last None -> vd.v_last in

      if Env.mem vd.v_ident h then
        error (Ealready_defined(sourcename vd.v_ident));

      let acc_defined = Env.add vd.v_ident ty acc_defined in
      let h = Env.add vd.v_ident { ty = ty; last = last vd.v_last } h in
      { vd with v_last = last_dec; v_type = ty }, (acc_defined, h)
    with
        TypingError(kind) -> message vd.v_loc kind
  in
    mapfold var_dec (Env.empty, h) dec

let typing_contract const_env h contract =

  match contract with
    | None -> None,h
    | Some ({ c_block = b;
              c_assume = e_a;
              c_enforce = e_g }) ->
        let typed_b, defined_names, _ = typing_block const_env h b in
          (* check that the equations do not define other unexpected names *)
          included_env defined_names Env.empty;

        (* assumption *)
        let typed_e_a = expect const_env h (Tid Initial.pbool) e_a in
        (* property *)
        let typed_e_g = expect const_env h (Tid Initial.pbool) e_g in

          Some { c_block = typed_b;
                 c_assume = typed_e_a;
                 c_enforce = typed_e_g }, h

let solve loc cl =
  try
    solve QualEnv.empty cl
  with
      Solve_failed c -> message loc (Econstraint_solve_failed c)

let build_node_params const_env l =
  let check_param env p =
    let ty = check_type const_env p.p_type in
    let p = { p with p_type = ty } in
    let n = Names.local_qn p.p_name in
    p, QualEnv.add n ty env
  in
    mapfold check_param const_env l

let node ({ n_name = f; n_statefull = statefull;
            n_input = i_list; n_output = o_list;
            n_contract = contract;
            n_block = b; n_loc = loc;
            n_params = node_params; } as n) =
  try
    let typed_params, const_env =
      build_node_params QualEnv.empty node_params in
    let typed_i_list, (input_names, h) =
      build const_env Env.empty i_list in
    let typed_o_list, (output_names, h) = build const_env h o_list in

    (* typing contract *)
    let typed_contract, h =
      typing_contract const_env h contract in

    let typed_b, defined_names, _ = typing_block const_env h b in
      (* check that the defined names match exactly the outputs and locals *)
      included_env defined_names output_names;
      included_env output_names defined_names;

    (* update the node signature to add static params constraints *)
    let cl = get_size_constraint () in
    let cl = solve loc cl in
    let s = find_value f in
    replace_value f { s with node_params_constraints = cl };

    { n with
        n_input = typed_i_list;
        n_output = typed_o_list;
        n_params = typed_params;
        n_contract = typed_contract;
        n_block = typed_b }
  with
    | TypingError(error) -> message loc error

let typing_const_dec cd =
  let ty = check_type QualEnv.empty cd.c_type in
  let se = expect_static_exp QualEnv.empty ty cd.c_value in
  let cd = { cd with c_value = se; c_type = ty } in
    add_const cd.c_name (mk_const_def cd.c_type cd.c_value);
    cd

let program
    ({ p_opened = opened; p_types = p_type_list;
       p_nodes = p_node_list; p_consts = p_consts_list } as p) =
  let typed_cd_list = List.map typing_const_dec p_consts_list in
  let typed_node_list = List.map node p_node_list in
    { p with p_nodes = typed_node_list; p_consts = typed_cd_list }
