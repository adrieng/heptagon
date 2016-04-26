(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)
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
open Pp_tools
open Format

type value = { vd: var_dec; mutable last: bool }

type error =
  | Emissing of name
  | Emissingcase of name
  | Eundefined of name
  | Elast_undefined of name
  | Etype_clash of ty * ty
  | Eargs_clash of ty * ty
  | Earity_clash of int * int
  | Estatic_arity_clash of int * int
  | Ealready_defined of name
  | Enon_exaustive
  | Epartial_switch of name
  | Etoo_many_outputs
  | Ebad_pervasives
  | Esome_fields_are_missing
  | Esubscripted_value_not_an_array of ty
  | Earray_subscript_should_be_const
  | Eundefined_const of qualname
  | Econstraint_solve_failed of constrnt
  | Etype_should_be_static of ty
  | Erecord_type_expected of ty
  | Eno_such_field of ty * qualname
  | Eempty_record
  | Eempty_array
  | Efoldi_bad_args of ty
  | Emapi_bad_args of ty
  | Emerge_missing_constrs of QualSet.t
  | Emerge_uniq of qualname
  | Emerge_mix of qualname
  | Estatic_constraint of constrnt
  | Esplit_enum of ty
  | Esplit_tuple of ty
  | Eenable_memalloc
  | Ebad_format
  | Eformat_string_not_constant

exception Unify
exception TypingError of error

let error kind = raise (TypingError(kind))

let message loc kind =
  begin match kind with
    | Emissing(s) ->
        eprintf "%aNo equation is given for name %s.@."
          print_location loc
          s;
    | Emissingcase(s) ->
        eprintf "%aCase %s not defined.@."
          print_location loc
          s;
    | Eundefined(s) ->
        eprintf "%aThe name %s is unbound.@."
          print_location loc
          s;
    | Elast_undefined(s) ->
        eprintf "%aThe name %s does not have a last value.@."
          print_location loc
          s;
    | Etype_clash(actual_ty, expected_ty) ->
        eprintf "%aType Clash: this expression has type %a, @\n\
            but is expected to have type %a.@."
          print_location loc
          print_type actual_ty
          print_type expected_ty
    | Eargs_clash(actual_ty, expected_ty) ->
        eprintf "%aType Clash: arguments of type %a were given, @\n\
            but %a was expected.@."
          print_location loc
          print_type actual_ty
          print_type expected_ty
    | Earity_clash(actual_arit, expected_arit) ->
        eprintf "%aType Clash: this expression expects %d arguments,@\n\
            but is expected to have %d.@."
          print_location loc
          expected_arit actual_arit
    | Estatic_arity_clash(actual_arit, expected_arit) ->
        eprintf "%aType Clash: this node expects %d static parameters,@\n\
            but was given %d.@."
          print_location loc
          expected_arit actual_arit
    | Ealready_defined(s) ->
        eprintf "%aThe name %s is already defined.@."
          print_location loc
          s
    | Emerge_missing_constrs c_set ->
        eprintf "%aSome constructors are missing in this merge : @[%a@]@."
          print_location loc
          (print_list_r print_qualname """,""") (QualSet.elements c_set)
    | Emerge_uniq c ->
        eprintf "%aThe constructor %a is matched more than one time.@."
          print_location loc
          print_qualname c
    | Emerge_mix c ->
        eprintf "%aYou can't mix constructors from different types.@\n\
          The constructor %a is unexpected.@."
          print_location loc
          print_qualname c
    | Enon_exaustive ->
        eprintf "%aSome constructors are missing in this pattern/matching.@."
          print_location loc
    | Epartial_switch(s) ->
        eprintf "%aThe case %s is missing.@."
          print_location loc
          s
    | Etoo_many_outputs ->
        eprintf "%aA function may only return a basic value.@."
          print_location loc
    | Ebad_pervasives ->
        eprintf "%aNo nodes or multiple return values allowed in Pervasives.@."
          print_location loc
    | Esome_fields_are_missing ->
        eprintf "%aSome fields are missing.@."
          print_location loc
    | Esubscripted_value_not_an_array  ty ->
        eprintf "%aSubscript used on a non array type : %a.@."
          print_location loc
          Global_printer.print_type ty
    | Earray_subscript_should_be_const ->
        eprintf "%aSubscript has to be a static value.@."
          print_location loc
    | Eundefined_const ln ->
        eprintf "%aThe const name '%s' is unbound.@."
          print_location loc
          (fullname ln)
    | Econstraint_solve_failed c ->
        eprintf "%aThe following constraint cannot be satisified:@\n%a.@."
          print_location loc
          print_constrnt c
    | Etype_should_be_static ty ->
        eprintf "%aThis type should be static : %a.@."
          print_location loc
          print_type ty
    | Erecord_type_expected ty ->
        eprintf "%aA record was expected (found %a).@."
          print_location loc
          print_type ty
    | Eno_such_field (ty, f) ->
        eprintf "%aThe record type '%a' does not have a '%s' field.@."
          print_location loc
          print_type ty
          (shortname f)
    | Eempty_record ->
        eprintf "%aThe record is empty.@."
          print_location loc
    | Eempty_array ->
        eprintf "%aThe array is empty.@."
          print_location loc
    | Efoldi_bad_args  ty ->
        eprintf
          "%aThe function given to foldi should expect an integer \
               as the last but one argument (found: %a).@."
          print_location loc
          print_type ty
    | Emapi_bad_args  ty ->
        eprintf
          "%aThe function given to mapi should expect an integer \
               as the last argument (found: %a).@."
          print_location loc
          print_type ty
    | Estatic_constraint c ->
        eprintf "%aThis application doesn't respect the static constraint :@\n%a.@."
          print_location loc
          print_static_exp c
    | Esplit_enum ty ->
        eprintf
          "%aThe first argument of split has to be an \
               enumerated type (found: %a).@."
          print_location loc
          print_type ty
    | Esplit_tuple ty ->
        eprintf
          "%aThe second argument of spit cannot \
               be a tuple (found: %a).@."
          print_location loc
          print_type ty
    | Eenable_memalloc ->
      eprintf
        "%aThis function was compiled with linear types. \
               Enable linear typing to call it.@."
          print_location loc
    | Ebad_format ->
      eprintf
        "%aThe format string is invalid@."
          print_location loc
    | Eformat_string_not_constant ->
      eprintf
        "%aA static format string was expected@."
          print_location loc
  end;
  raise Errors.Error

(** Add wrappers around Modules function to raise errors
    and display the correct location. *)
let find_with_error find_fun f =
  try find_fun f
  with Not_found -> error (Eundefined(fullname f))

let find_value v = find_with_error find_value v
let find_constrs c = Tid (find_with_error find_constrs c)
let find_field f = find_with_error find_field f


(** Helper functions to work with types *)
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

let flatten_ty_list l =
  List.fold_right
    (fun arg args -> match arg with Tprod l -> l@args | a -> a::args ) l []

let kind f ty_desc =
  let ty_of_arg v =
    if Linearity.is_linear v.a_linearity && not !Compiler_options.do_linear_typing then
      error Eenable_memalloc;
    v.a_type
  in
  let op = if ty_desc.node_stateful then Enode f else Efun f in
    op, List.map ty_of_arg ty_desc.node_inputs,
  List.map ty_of_arg ty_desc.node_outputs

let typ_of_name h x =
  try
    let { vd = vd } = Env.find x h in vd.v_type
  with
      Not_found -> error (Eundefined(name x))

let vd_of_name h x =
  try
    let { vd = vd } = Env.find x h in vd
  with
      Not_found -> error (Eundefined(name x))

let desc_of_ty = function
  | Tid n when n = pbool  -> Tenum [ptrue; pfalse]
  | Tid ty_name -> find_type ty_name
  | _  -> Tabstract
let set_of_constr = function
  | Tabstract | Tstruct _ | Talias _ -> assert false
  | Tenum tag_list -> List.fold_right QualSet.add tag_list QualSet.empty

let build_subst names values =
  if List.length names <> List.length values
  then error (Estatic_arity_clash (List.length values, List.length names));
  List.fold_left2 (fun m n v -> QualEnv.add n v m)
    QualEnv.empty names values

let add_distinct_env id vd env =
  if Env.mem id env then
    error (Ealready_defined(name id))
  else
    Env.add id vd env

let add_distinct_qualset n acc =
  if QualSet.mem n acc then
    error (Ealready_defined (fullname n))
  else
    QualSet.add n acc

let add_distinct_S n acc =
  if NamesSet.mem n acc then
    error (Ealready_defined n)
  else
    NamesSet.add n acc

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
    (fun elt _ -> if not (Env.mem elt s2) then error (Emissing(name elt)))
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
      Env.fold (fun elt vd env ->
                  if not (Env.mem elt total) then Env.add elt vd env
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
       then error (Elast_undefined(name elt)))
    env

let last = function | Var -> false | Last _ -> true

(** Checks that a field is not defined twice in a list
    of field name, exp.*)
let check_field_unicity l =
  let add_field acc (f,e) =
    if NamesSet.mem (shortname f) acc then
      message e.e_loc (Ealready_defined (fullname f))
    else
      NamesSet.add (shortname f) acc
  in
  ignore (List.fold_left add_field NamesSet.empty l)

(** Checks that a field is not defined twice in a list
    of field name, exp.*)
let check_static_field_unicity l =
  let add_field acc (f,se) =
    if NamesSet.mem (shortname f) acc then
      message se.se_loc (Ealready_defined (fullname f))
    else
      NamesSet.add (shortname f) acc
  in
  ignore (List.fold_left add_field NamesSet.empty l)

(** @return the qualified name and list of fields of
    the type with name [n].
    Prints an error message if the type is not a record type.
    [loc] is the location used for error reporting.*)
let struct_info_from_name n =
  try
    find_struct n
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
    let t = find_field f in
    t, struct_info_from_name t
  with
      Not_found -> error (Eundefined (fullname f))

let rec _unify cenv t1 t2 =
  match t1, t2 with
    | b1, b2 when b1 = b2 -> ()
    | Tprod t1_list, Tprod t2_list ->
        (try
           List.iter2 (_unify cenv) t1_list t2_list
         with
             _ -> raise Unify
        )
    | Tarray (ty1, e1), Tarray (ty2, e2) ->
        (try
           add_constraint_eq ~unsafe:true cenv e1 e2
         with Solve_failed _ ->
           raise Unify);
        _unify cenv ty1 ty2
    | _ -> raise Unify

(** {3 Constraints related functions} *)
and (curr_constrnt : constrnt list ref) = ref []

and solve ?(unsafe=false) c_l =
  try Static.solve Names.QualEnv.empty c_l
  with Solve_failed c ->
    if unsafe then
      raise (Solve_failed c)
    else
      error (Estatic_constraint c)

(** [cenv] is the constant env which will be used to simplify the given constraints *)
and add_constraint ?(unsafe=false) cenv c =
  let c = expect_static_exp cenv Initial.tbool c in
  curr_constrnt := (solve ~unsafe:unsafe [c])@(!curr_constrnt)

(** Add the constraint [c1=c2] *)
and add_constraint_eq ?(unsafe=false) cenv c1 c2 =
  let c = mk_static_exp tbool (Sop (mk_pervasives "=",[c1;c2])) in
  add_constraint ~unsafe:unsafe cenv c

(** Add the constraint [c1<=c2] *)
and add_constraint_leq cenv c1 c2 =
  let c = mk_static_exp tbool (Sop (mk_pervasives "<=",[c1;c2])) in
  add_constraint cenv c


and get_constraints () =
  let l = !curr_constrnt in
  curr_constrnt := [];
  l

and unify cenv t1 t2 =
  let ut1 = unalias_type t1 in
  let ut2 = unalias_type t2 in
  try _unify cenv ut1 ut2 with Unify -> error (Etype_clash(t1, t2))


(** [check_type t] checks that t exists *)
and check_type cenv = function
  | Tarray(ty, e) ->
      let typed_e = expect_static_exp cenv (Tid Initial.pint) e in
      Tarray(check_type cenv ty, typed_e)
  (* No need to check that the type is defined as it is done by the scoping. *)
  | Tid ty_name -> Tid ty_name
  | Tprod l -> Tprod (List.map (check_type cenv) l)
  | Tinvalid -> Tinvalid

and typing_static_exp cenv se =
  try
  let desc, ty = match se.se_desc with
    | Sint v -> Sint v, Tid Initial.pint
    | Sbool v-> Sbool v, Tid Initial.pbool
    | Sfloat v -> Sfloat v, Tid Initial.pfloat
    | Sstring v -> Sstring v, Tid Initial.pstring
    | Svar ln ->
        (try (* this can be a global const*)
           let cd = Modules.find_const ln in
             Svar ln, cd.Signature.c_type
         with Not_found -> (* or a static parameter *)
           Svar ln, QualEnv.find ln cenv)
    | Sconstructor c -> Sconstructor c, find_constrs c
    | Sfield c -> Sfield c, Tid (find_field c)
    | Sop ({name = "="} as op, se_list) ->
        let se1, se2 = assert_2 se_list in
        let typed_se1, t1 = typing_static_exp cenv se1 in
        let typed_se2 = expect_static_exp cenv t1 se2 in
        Sop (op, [typed_se1;typed_se2]), Tid Initial.pbool
    | Sop (op, se_list) ->
        let ty_desc = find_value op in
        let typed_se_list = typing_static_args cenv
          (types_of_arg_list ty_desc.node_inputs) se_list
        in
        Sop (op, typed_se_list),
        prod (types_of_arg_list ty_desc.node_outputs)
    | Sarray_power (se, n_list) ->
        let typed_n_list = List.map (expect_static_exp cenv Initial.tint) n_list in
        let typed_se, ty = typing_static_exp cenv se in
        let tarray = List.fold_left (fun ty typed_n -> Tarray(ty, typed_n)) ty typed_n_list in
          Sarray_power (typed_se, typed_n_list), tarray
    | Sarray [] ->
        message se.se_loc Eempty_array
    | Sarray (se::se_list) ->
        let typed_se, ty = typing_static_exp cenv se in
        let typed_se_list = List.map (expect_static_exp cenv ty) se_list in
        Sarray (typed_se::typed_se_list),
        Tarray(ty, mk_static_int ((List.length se_list) + 1))
    | Stuple se_list ->
        let typed_se_list, ty_list = List.split
          (List.map (typing_static_exp cenv) se_list) in
        Stuple typed_se_list, prod ty_list
    | Srecord f_se_list ->
        (* find the record type using the first field *)
        let q, fields =
          (match f_se_list with
             | [] -> error (Eempty_record)
             | (f,_)::_ -> struct_info_from_field f
          ) in
          check_static_field_unicity f_se_list;
          if List.length f_se_list <> List.length fields then
            message se.se_loc Esome_fields_are_missing;
          let f_se_list =
            List.map (typing_static_field cenv fields
                        (Tid q)) f_se_list in
          Srecord f_se_list, Tid q
  in
   { se with se_ty = ty; se_desc = desc }, ty

  with
      TypingError kind -> message se.se_loc kind

and typing_static_field cenv fields t1 (f,se) =
  try
    let ty = check_type cenv (field_assoc f fields) in
    let typed_se = expect_static_exp cenv ty se in
      f, typed_se
  with
      Not_found -> message se.se_loc (Eno_such_field (t1, f))

and typing_static_args cenv expected_ty_list e_list =
  try
    List.map2 (expect_static_exp cenv) expected_ty_list e_list
  with Invalid_argument _ ->
    error (Earity_clash(List.length e_list, List.length expected_ty_list))

and expect_static_exp cenv exp_ty se =
  let se, ty = typing_static_exp cenv se in
    try
      unify cenv ty exp_ty; se
    with
      _ -> message se.se_loc (Etype_clash(ty, exp_ty))


(** @return the type of the field with name [f] in the list
    [fields]. [t1] is the corresponding record type and [loc] is
    the location, both used for error reporting. *)
let field_type cenv f fields t1 loc =
  try
    check_type cenv (field_assoc f fields)
  with
      Not_found -> message loc (Eno_such_field (t1, f))

let rec typing cenv h e =
  try
    let typed_desc,ty = match e.e_desc with
      | Econst c ->
          let typed_c, ty = typing_static_exp cenv c in
            Econst typed_c, ty
      | Evar x ->
          Evar x, typ_of_name h x
      | Elast x ->
          Elast x, typ_of_name h x

      | Eapp(op, e_list, r) ->
          let ty, op, typed_e_list =
            typing_app cenv h op e_list in
            Eapp(op, typed_e_list, r), ty

      | Estruct(l) ->
          (* find the record type using the first field *)
          let q, fields =
            (match l with
               | [] -> message e.e_loc (Eempty_record)
               | (f,_)::_ -> struct_info_from_field f
            ) in

          if List.length l <> List.length fields
          then message e.e_loc Esome_fields_are_missing;
          check_field_unicity l;
          let l = List.map (typing_field cenv h fields (Tid q)) l in
          Estruct l, Tid q

      | Epre (None, e) ->
          let typed_e,ty = typing cenv h e in
            Epre (None, typed_e), ty

      | Epre (Some c, e) ->
          let typed_c, t1 = typing_static_exp cenv c in
          let typed_e = expect cenv h t1 e in
            Epre(Some typed_c, typed_e), t1

      | Efby (e1, e2) ->
          let typed_e1, t1 = typing cenv h e1 in
          let typed_e2 = expect cenv h t1 e2 in
            Efby (typed_e1, typed_e2), t1

      | Eiterator (it, ({ a_op = (Enode f | Efun f);
                          a_params = params } as app),
                   n_list, pe_list, e_list, reset) ->
          let ty_desc = find_value f in
          let op, expected_ty_list, result_ty_list = kind f ty_desc in
          let node_params =
            List.map (fun { p_name = n } -> local_qn n) ty_desc.node_params in
          let m = build_subst node_params params in
          let expected_ty_list =
            List.map (simplify_type m) expected_ty_list in
          let result_ty_list = List.map (simplify_type m) result_ty_list in
          let typed_n_list = List.map (expect_static_exp cenv (Tid Initial.pint)) n_list in
          (*typing of partial application*)
          let p_ty_list, expected_ty_list =
            Misc.split_at (List.length pe_list) expected_ty_list in
          let typed_pe_list = typing_args cenv h p_ty_list pe_list in
          (*typing of other arguments*)
          let ty, typed_e_list = typing_iterator cenv h it typed_n_list
            expected_ty_list result_ty_list e_list in
          let typed_params = typing_node_params cenv
            ty_desc.node_params params in
          (* add size constraints *)
          let constrs = List.map (simplify m) ty_desc.node_param_constraints in
          List.iter (fun n -> add_constraint_leq cenv (mk_static_int 1) n) typed_n_list;
          List.iter (add_constraint cenv) constrs;
          (* return the type *)
          Eiterator(it, { app with a_op = op; a_params = typed_params }
                      , typed_n_list, typed_pe_list, typed_e_list, reset), ty
      | Eiterator _ -> assert false

      | Ewhen (e, c, x) ->
          let typed_e, t = typing cenv h e in
          let tn_expected = find_constrs c in
          let tn_actual = typ_of_name h x in
          unify cenv tn_actual tn_expected;
          Ewhen (typed_e, c, x), t

      | Emerge (x, (c1,e1)::c_e_list) ->
          (* verify the constructors : they should be unique,
               all of the same type and cover all the possibilities *)
          let c_type = find_constrs c1 in
          let c_set = QualSet.singleton c1 in
          let c_set =
            List.fold_left
              (fun c_set (c, _) ->
                if QualSet.mem c c_set then message e.e_loc (Emerge_uniq c);
                (try unify cenv c_type (find_constrs c)
                with
                  TypingError(Etype_clash _) -> message e.e_loc (Emerge_mix c));
                QualSet.add c c_set) c_set c_e_list in
          let expected_c_set =
            let expected_c_list =
              match c_type with
                | Tid tc ->
                    (match find_type tc with Tenum cl-> cl | _ -> assert false)
                | _ -> assert false (* type of constrs are Tenum *) in
            List.fold_left
              (fun acc c -> QualSet.add c acc) QualSet.empty expected_c_list in
          let c_set_diff = QualSet.diff expected_c_set c_set in
          if not (QualSet.is_empty c_set_diff)
          then message e.e_loc (Emerge_missing_constrs c_set_diff);
          (* verify [x] is of the right type *)
          unify cenv (typ_of_name h x) c_type;
          (* type *)
          let typed_e1, t = typing cenv h e1 in
          let typed_c_e_list =
            List.map (fun (c, e) -> (c, expect cenv h t e)) c_e_list in
          Emerge (x, (c1,typed_e1)::typed_c_e_list), t
      | Emerge (_, []) -> assert false

      | Esplit(c, e2) ->
          let typed_c, ty_c = typing cenv h c in
          let typed_e2, ty = typing cenv h e2 in
          let n =
            match ty_c with
              | Tid tc ->
                  (match find_type tc with | Tenum cl-> List.length cl | _ -> -1)
              | _ ->  -1 in
            if n < 0 then
              message e.e_loc (Esplit_enum ty_c);
            (*the type of e should not be a tuple *)
            (match ty with
              | Tprod _ -> message e.e_loc (Esplit_tuple ty)
              | _ -> ());
            Esplit(typed_c, typed_e2), Tprod (repeat_list ty n)
    in
      { e with e_desc = typed_desc; e_ty = ty; }, ty
  with
      TypingError(kind) -> message e.e_loc kind

and typing_field cenv h fields t1 (f, e) =
  try
    let ty = check_type cenv (field_assoc f fields) in
    let typed_e = expect cenv h ty e in
      f, typed_e
  with
      Not_found -> message e.e_loc (Eno_such_field (t1, f))

and expect cenv h expected_ty e =
  let typed_e, actual_ty = typing cenv h e in
  try
    unify cenv actual_ty expected_ty;
    typed_e
  with TypingError(kind) -> message e.e_loc kind

and typing_app cenv h app e_list =
  match app.a_op with
    | Earrow ->
        let e1, e2 = assert_2 e_list in
        let typed_e1, t1 = typing cenv h e1 in
        let typed_e2 = expect cenv h t1 e2 in
        t1, app, [typed_e1;typed_e2]

    | Eifthenelse ->
        let e1, e2, e3 = assert_3 e_list in
        let typed_e1 = expect cenv h
          (Tid Initial.pbool) e1 in
        let typed_e2, t1 = typing cenv h e2 in
        let typed_e3 = expect cenv h t1 e3 in
        t1, app, [typed_e1; typed_e2; typed_e3]

    | Efun {name = "="} ->
        let e1, e2 = assert_2 e_list in
        let typed_e1, t1 = typing cenv h e1 in
        let typed_e2 = expect cenv h t1 e2 in
        Tid Initial.pbool, app, [typed_e1; typed_e2]

    | Efun { qual = Module "Iostream"; name = "printf" } ->
        let e1, format_args = assert_1min e_list in
        let typed_e1 = expect cenv h Initial.tstring e1 in
        let typed_format_args = typing_format_args cenv h typed_e1 format_args in
        Tprod [], app, typed_e1::typed_format_args

    | Efun { qual = Module "Iostream"; name = "fprintf" } ->
        let e1, e2, format_args = assert_2min e_list in
        let typed_e1 = expect cenv h Initial.tfile e1 in
        let typed_e2 = expect cenv h Initial.tstring e2 in
        let typed_format_args = typing_format_args cenv h typed_e1 format_args in
        Tprod [], app, typed_e1::typed_e2::typed_format_args

    | (Efun f | Enode f) ->
        let ty_desc = find_value f in
        let op, expected_ty_list, result_ty_list = kind f ty_desc in
        let node_params = List.map (fun { p_name = n } -> local_qn n) ty_desc.node_params in
        let m = build_subst node_params app.a_params in
        let expected_ty_list = List.map (simplify_type m) expected_ty_list in
        let typed_e_list = typing_args cenv h expected_ty_list e_list in
        let result_ty_list = List.map (simplify_type m) result_ty_list in
        (* Type static parameters and generate constraints *)
        let typed_params = typing_node_params cenv ty_desc.node_params app.a_params in
        let constrs = List.map (simplify m) ty_desc.node_param_constraints in
        List.iter (add_constraint cenv) constrs;
        prod result_ty_list,
        { app with a_op = op; a_params = typed_params },
         typed_e_list

    | Etuple ->
        let typed_e_list,ty_list =
          List.split (List.map (typing cenv h) e_list) in
         prod ty_list, app, typed_e_list

    | Earray ->
        let exp, e_list = assert_1min e_list in
        let typed_exp, t1 = typing cenv h exp in
        let typed_e_list = List.map (expect cenv h t1) e_list in
        let n = mk_static_int (List.length e_list + 1) in
          Tarray(t1, n), app, typed_exp::typed_e_list

    | Efield ->
        let e = assert_1 e_list in
        let f = assert_1 app.a_params in
        let fn =
          (match f.se_desc with
             | Sfield fn -> fn
             | _ -> assert false) in
        let typed_e, t1 = typing cenv h e in
        let fields = struct_info t1 in
        let t2 = field_type cenv fn fields t1 e.e_loc in
          t2, app, [typed_e]

    | Efield_update ->
        let e1, e2 = assert_2 e_list in
        let f = assert_1 app.a_params in
        let typed_e1, t1 = typing cenv h e1 in
        let fields = struct_info t1 in
        let fn =
          (match f.se_desc with
             | Sfield fn -> fn
             | _ -> assert false) in
        let t2 = field_type cenv fn fields t1 e1.e_loc in
        let typed_e2 = expect cenv h t2 e2 in
        t1, app, [typed_e1; typed_e2]

    | Earray_fill ->
        let _, _ = assert_1min app.a_params in
        let e1 = assert_1 e_list in
        let typed_n_list = List.map (expect_static_exp cenv Initial.tint) app.a_params in
        let typed_e1, t1 = typing cenv h e1 in
        List.iter (fun typed_n -> add_constraint_leq cenv (mk_static_int 1) typed_n) typed_n_list;
        (List.fold_left (fun t1 typed_n -> Tarray (t1, typed_n)) t1 typed_n_list),
          { app with a_params = typed_n_list }, [typed_e1]

    | Eselect ->
        let e1 = assert_1 e_list in
        let typed_e1, t1 = typing cenv h e1 in
        let typed_idx_list, ty =
          typing_array_subscript cenv h app.a_params t1 in
          ty, { app with a_params = typed_idx_list }, [typed_e1]

    | Eselect_dyn ->
        let e1, defe, idx_list = assert_2min e_list in
        let typed_e1, t1 = typing cenv h e1 in
        let typed_defe = expect cenv h (element_type t1) defe in
        let ty, typed_idx_list =
          typing_array_subscript_dyn cenv h idx_list t1 in
        ty, app, typed_e1::typed_defe::typed_idx_list

    | Eselect_trunc ->
        let e1, idx_list = assert_1min e_list in
        let typed_e1, t1 = typing cenv h e1 in
        let ty, typed_idx_list =
          typing_array_subscript_dyn cenv h idx_list t1 in
        ty, app, typed_e1::typed_idx_list

    | Eupdate ->
        let e1, e2, idx_list = assert_2min e_list in
        let typed_e1, t1 = typing cenv h e1 in
        let ty, typed_idx_list =
          typing_array_subscript_dyn cenv h idx_list t1 in
        let typed_e2 = expect cenv h ty e2 in
          t1, app, typed_e1::typed_e2::typed_idx_list

    | Eselect_slice ->
        let e = assert_1 e_list in
        let idx1, idx2 = assert_2 app.a_params in
        let typed_idx1 = expect_static_exp cenv (Tid Initial.pint) idx1 in
        let typed_idx2 = expect_static_exp cenv (Tid Initial.pint) idx2 in
        let typed_e, t1 = typing cenv h e in
        (*Create the expression to compute the size of the array *)
        let e1 = mk_static_int_op (mk_pervasives "-") [typed_idx2; typed_idx1] in
        let e2 = mk_static_int_op (mk_pervasives "+") [e1;mk_static_int 1 ] in
        add_constraint_leq cenv (mk_static_int 1) e2;
        Tarray (element_type t1, e2),
        { app with a_params = [typed_idx1; typed_idx2] }, [typed_e]

    | Econcat ->
        let e1, e2 = assert_2 e_list in
        let typed_e1, t1 = typing cenv h e1 in
        let typed_e2, t2 = typing cenv h e2 in
        begin try
          unify cenv (element_type t1) (element_type t2)
        with
            TypingError(kind) -> message e1.e_loc kind
        end;
        let n =
          mk_static_int_op (mk_pervasives "+") [array_size t1; array_size t2] in
        Tarray (element_type t1, n), app, [typed_e1; typed_e2]

      | Ereinit ->
        let e1, e2 = assert_2 e_list in
        let typed_e1, ty = typing cenv h e1 in
        let typed_e2 = expect cenv h ty e2 in
        ty, app, [typed_e1; typed_e2]

and typing_iterator cenv h
    it n_list args_ty_list result_ty_list e_list =
  let rec array_of_idx_list l ty = match l with
    | [] -> ty
    | n::l -> array_of_idx_list l (Tarray(ty, n))
  in
  let mk_array_type ty_list = List.map (array_of_idx_list n_list) ty_list in
  let n_size = List.length n_list in
  let mk_array_type_butlast ty_list =
    map_butlast (array_of_idx_list n_list) ty_list in
  match it with
  | Imap ->
      let args_ty_list = mk_array_type args_ty_list in
      let result_ty_list = mk_array_type result_ty_list in
      let typed_e_list = typing_args cenv h
        args_ty_list e_list in
      prod result_ty_list, typed_e_list

  | Imapi ->
      let args_ty_list, idx_ty_list = split_nlast n_size args_ty_list in
      let args_ty_list = mk_array_type args_ty_list in
      let result_ty_list = mk_array_type result_ty_list in
      (* Last but one arg of the function should be integer *)
        List.iter
          (fun idx_ty ->
            ( try unify cenv idx_ty (Tid Initial.pint)
              with TypingError _ -> raise (TypingError (Emapi_bad_args idx_ty))))
           idx_ty_list;
      let typed_e_list = typing_args cenv h
        args_ty_list e_list in
      prod result_ty_list, typed_e_list

  | Ifold ->
      let args_ty_list = mk_array_type_butlast args_ty_list in
      let typed_e_list =
        typing_args cenv h args_ty_list e_list in
      (*check accumulator type matches in input and output*)
      if List.length result_ty_list > 1 then error Etoo_many_outputs;
      ( try unify cenv (last_element args_ty_list) (List.hd result_ty_list)
        with TypingError(kind) -> message (List.hd e_list).e_loc kind );
      (List.hd result_ty_list), typed_e_list

  | Ifoldi ->
      let args_ty_list, acc_ty = split_last args_ty_list in
      let args_ty_list, idx_ty_list = split_nlast n_size args_ty_list in
        (* Last but one arg of the function should be integer *)
        List.iter
          (fun idx_ty ->
            ( try unify cenv idx_ty (Tid Initial.pint)
              with TypingError _ -> raise (TypingError (Emapi_bad_args idx_ty))))
           idx_ty_list;
        let args_ty_list = mk_array_type_butlast (args_ty_list@[acc_ty]) in
      let typed_e_list =
        typing_args cenv h args_ty_list e_list in
      (*check accumulator type matches in input and output*)
      if List.length result_ty_list > 1 then error Etoo_many_outputs;
      ( try unify cenv (last_element args_ty_list) (List.hd result_ty_list)
        with TypingError(kind) -> message (List.hd e_list).e_loc kind );
      (List.hd result_ty_list), typed_e_list

    | Imapfold ->
      let args_ty_list = mk_array_type_butlast args_ty_list in
      let result_ty_list = mk_array_type_butlast result_ty_list in
      let typed_e_list = typing_args cenv h
        args_ty_list e_list in
      (*check accumulator type matches in input and output*)
      ( try unify cenv (last_element args_ty_list) (last_element result_ty_list)
        with TypingError(kind) -> message (List.hd e_list).e_loc kind );
      prod result_ty_list, typed_e_list

and typing_array_subscript cenv h idx_list ty  =
  match unalias_type ty, idx_list with
    | ty, [] -> [], ty
    | Tarray(ty, exp), idx::idx_list ->
        ignore (expect_static_exp cenv (Tid Initial.pint) exp);
        let typed_idx = expect_static_exp cenv (Tid Initial.pint) idx in
        add_constraint_leq cenv (mk_static_int 0) idx;
        let bound = mk_static_int_op (mk_pervasives "-") [exp; mk_static_int 1] in
        add_constraint_leq cenv idx bound;
        let typed_idx_list, ty = typing_array_subscript cenv h idx_list ty in
        typed_idx::typed_idx_list, ty
    | _, _ -> raise (TypingError (Esubscripted_value_not_an_array ty))

(* This function checks that the array dimensions matches
   the subscript. It returns the base type wrt the nb of indices. *)
and typing_array_subscript_dyn cenv h idx_list ty =
  match unalias_type ty, idx_list with
    | ty, [] -> ty, []
    | Tarray(ty, _), idx::idx_list ->
        let typed_idx = expect cenv h (Tid Initial.pint) idx in
        let ty, typed_idx_list =
          typing_array_subscript_dyn cenv h idx_list ty in
        ty, typed_idx::typed_idx_list
    | _, _ -> raise (TypingError (Esubscripted_value_not_an_array ty))

and typing_args cenv h expected_ty_list e_list =
  let typed_e_list, args_ty_list =
    List.split (List.map (typing cenv h) e_list)
  in
  let args_ty_list = flatten_ty_list args_ty_list in
  (match args_ty_list, expected_ty_list with
    | [], [] -> ()
    | _, _ ->
      (try
        unify cenv (prod args_ty_list) (prod expected_ty_list)
      with _ ->
        raise (TypingError (Eargs_clash (prod args_ty_list, prod expected_ty_list)))
      )
  );
  typed_e_list

and typing_node_params cenv params_sig params =
  List.map2 (fun p_sig p -> expect_static_exp cenv
               p_sig.p_type p) params_sig params

and typing_format_args cenv h e args =
  let s = match e.e_desc with
    | Econst { se_desc = Sstring s } -> s
    | _ -> raise (TypingError Eformat_string_not_constant)
  in
  try
    let expected_ty_list = Printf_parser.types_of_format_string s in
    typing_args cenv h expected_ty_list args
  with
    | Printf_parser.Bad_format -> raise (TypingError Ebad_format)

let rec typing_pat h acc = function
  | Evarpat(x) ->
      let vd = vd_of_name h x in
      let acc = add_distinct_env x vd acc in
      acc, vd.v_type
  | Etuplepat(pat_list) ->
      let acc, ty_list =
        List.fold_right
          (fun pat (acc, ty_list) ->
             let acc, ty = typing_pat h acc pat in acc, ty :: ty_list)
          pat_list (acc, []) in
      acc, Tprod(ty_list)

let rec typing_eq cenv h acc eq =
  let typed_desc,acc = match eq.eq_desc with
    | Eautomaton(state_handlers) ->
        let typed_sh,acc =
          typing_automaton_handlers cenv h acc state_handlers in
        Eautomaton(typed_sh),
        acc
    | Eswitch(e, switch_handlers) ->
        let typed_e,ty = typing cenv h e in
        let typed_sh,acc =
          typing_switch_handlers cenv h acc ty switch_handlers in
        Eswitch(typed_e,typed_sh),
        acc
    | Epresent(present_handlers, b) ->
        let typed_b, def_names, _ = typing_block cenv h b in
        let typed_ph, acc =
          typing_present_handlers cenv h
            acc def_names present_handlers in
        Epresent(typed_ph,typed_b),
        acc
    | Ereset(b, e) ->
        let typed_e = expect cenv h (Tid Initial.pbool) e in
        let typed_b, def_names, _ = typing_block cenv h b in
        Ereset(typed_b, typed_e),
        Env.union def_names acc
    | Eblock b ->
        let typed_b, def_names, _ = typing_block cenv h b in
        Eblock typed_b,
        Env.union def_names acc
    | Eeq(pat, e) ->
        let acc, ty_pat = typing_pat h acc pat in
        let typed_e = expect cenv h ty_pat e in
        Eeq(pat, typed_e),
        acc in
  { eq with eq_desc = typed_desc }, acc

and typing_eq_list cenv h acc eq_list =
  mapfold (typing_eq cenv h) acc eq_list

and typing_automaton_handlers cenv h acc state_handlers =
  (* checks unicity of states *)
  let addname acc { s_state = n } =
    add_distinct_S n acc in
  let states =  List.fold_left addname NamesSet.empty state_handlers in

  let escape h ({ e_cond = e; e_next_state = n } as esc) =
    if not (NamesSet.mem n states) then error (Eundefined(n));
    let typed_e = expect cenv h (Tid Initial.pbool) e in
    { esc with e_cond = typed_e } in

  let handler ({ s_block = b; s_until = e_list1;
                 s_unless = e_list2 } as s) =
    let typed_b, defined_names, h0 = typing_block cenv h b in
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

and typing_switch_handlers cenv h acc ty switch_handlers =
  (* checks unicity of states *)
  let addname acc { w_name = n } = add_distinct_qualset n acc in
  let cases = List.fold_left addname QualSet.empty switch_handlers in
  let d = diff_const (set_of_constr (desc_of_ty ty)) cases in
  if not (QualSet.is_empty d) then
    error (Epartial_switch (fullname (QualSet.choose d)));

  let handler ({ w_block = b } as sh) =
    let typed_b, defined_names, _ = typing_block cenv h b in
    { sh with w_block = typed_b }, defined_names in

  let typed_switch_handlers, defined_names_list =
    List.split (List.map handler switch_handlers) in
  let total, partial = merge defined_names_list in
  all_last h partial;
  (typed_switch_handlers,
   add total (add partial acc))

and typing_present_handlers cenv h acc def_names
    present_handlers =
  let handler ({ p_cond = e; p_block = b }) =
    let typed_e = expect cenv h (Tid Initial.pbool) e in
    let typed_b, defined_names, _ = typing_block cenv h b in
    { p_cond = typed_e; p_block = typed_b },
    defined_names
  in

  let typed_present_handlers, defined_names_list =
    List.split (List.map handler present_handlers) in
  let total, partial = merge (def_names :: defined_names_list) in
  all_last h partial;
  (typed_present_handlers,
   (add total (add partial acc)))

and typing_block cenv h
    ({ b_local = l; b_equs = eq_list; b_loc = loc } as b) =
  try
    let typed_l, (local_names, h0) = build cenv h l in
    let typed_eq_list, defined_names =
      typing_eq_list cenv h0 Env.empty eq_list in
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
and build cenv h dec =
  let var_dec (acc_defined, h) vd =
    try
      let ty = check_type cenv vd.v_type in

      let last_dec = match vd.v_last with
        | Last (Some se) -> Last (Some (expect_static_exp cenv ty se))
        | Var | Last None -> vd.v_last in

      if Env.mem vd.v_ident h then
        error (Ealready_defined(name vd.v_ident));

      let vd = { vd with v_last = last_dec; v_type = ty } in
      let acc_defined = Env.add vd.v_ident vd acc_defined in
      let h = Env.add vd.v_ident { vd = vd; last = last vd.v_last } h in
      vd, (acc_defined, h)
    with
        TypingError(kind) -> message vd.v_loc kind
  in
    mapfold var_dec (Env.empty, h) dec

let typing_objective cenv h obj =
  let typed_e = expect cenv h (Tid Initial.pbool) obj.o_exp in
  { obj with o_exp = typed_e }

let typing_contract cenv h contract =
  match contract with
    | None -> None,h
    | Some ({ c_block = b;
              c_assume = e_a;
              c_objectives = objs;
              c_assume_loc = e_a_loc;
              c_enforce_loc = e_g_loc;
              c_controllables = c }) ->
        let typed_b, defined_names, h' = typing_block cenv h b in
          (* check that the equations do not define other unexpected names *)
          included_env defined_names Env.empty;

        (* assumption *)
        let typed_e_a = expect cenv h' (Tid Initial.pbool) e_a in
        let typed_e_a_loc = expect cenv h' (Tid Initial.pbool) e_a_loc in
        (* objectives *)
        let typed_objs =
	  List.map
	    (fun o ->
	       let typed_exp = expect cenv h' (Tid Initial.pbool) o.o_exp in
	       { o with o_exp = typed_exp; })
	    objs in
        let typed_e_g_loc = expect cenv h' (Tid Initial.pbool) e_g_loc in

        let typed_c, (_c_names, h) = build cenv h c in

        Some { c_block = typed_b;
               c_assume = typed_e_a;
               c_objectives = typed_objs;
               c_assume_loc = typed_e_a_loc;
               c_enforce_loc = typed_e_g_loc;
               c_controllables = typed_c }, h


let build_node_params cenv l =
  let check_param env p =
    let ty = check_type env p.p_type in
    let p = { p with p_type = ty } in
    let n = Names.local_qn p.p_name in
    p, QualEnv.add n ty env
  in
    mapfold check_param cenv l

let typing_arg cenv a =
  { a with a_type = check_type cenv a.a_type }

let node ({ n_name = f; n_input = i_list; n_output = o_list;
            n_contract = contract;
            n_block = b; n_loc = loc;
            n_params = node_params; } as n) =
  try
    let typed_params, cenv =
      build_node_params QualEnv.empty node_params in
    let typed_i_list, (_input_names, h) = build cenv Env.empty i_list in
    let typed_o_list, (output_names, h) = build cenv h o_list in

    (* typing contract *)
    let typed_contract, h = typing_contract cenv h contract in

    let typed_b, defined_names, _ = typing_block cenv h b in
    (* check that the defined names match exactly the outputs and locals *)
    included_env defined_names output_names;
    included_env output_names defined_names;

    (* update the node signature to add static params constraints *)
    let s = find_value f in
    let cl = List.map (expect_static_exp cenv Initial.tbool) s.node_param_constraints in
    let cl = cl @ get_constraints () in
    let cl = solve cl in
    let node_inputs = List.map (typing_arg cenv) s.node_inputs in
    let node_outputs = List.map (typing_arg cenv) s.node_outputs in
    replace_value f { s with node_param_constraints = cl;
                             node_inputs = node_inputs; node_outputs = node_outputs };

    { n with
        n_input = typed_i_list;
        n_output = typed_o_list;
        n_params = typed_params;
        n_contract = typed_contract;
        n_block = typed_b }
  with
    | TypingError(error) -> message loc error

let typing_const_dec cd =
  let ty = check_type QualEnv.empty cd.Heptagon.c_type in
  let se = expect_static_exp QualEnv.empty ty cd.Heptagon.c_value in
  let const_def = { Signature.c_type = ty; Signature.c_value = se } in
    Modules.replace_const cd.c_name const_def;
    { cd with Heptagon.c_value = se; Heptagon.c_type = ty }

let typing_typedec td =
  let tydesc = match td.t_desc with
    | Type_abs -> Type_abs
    | Type_enum(tag_list) -> Type_enum tag_list
    | Type_alias t ->
        let t = check_type QualEnv.empty t in
          replace_type td.t_name (Talias t);
          Type_alias t
    | Type_struct(field_ty_list) ->
        let typing_field { f_name = f; f_type = ty } =
          { f_name = f; f_type = check_type QualEnv.empty ty }
        in
        let field_ty_list = List.map typing_field field_ty_list in
          replace_type td.t_name (Tstruct field_ty_list);
          Type_struct field_ty_list
  in
    { td with t_desc = tydesc }

let typing_signature s =
  let typed_params, cenv = build_node_params QualEnv.empty s.sig_params in
  if Modules.current () = Pervasives
       && (s.sig_stateful || List.length s.sig_outputs > 1)
    then message s.sig_loc Ebad_pervasives;
  { s with sig_params = typed_params;
    sig_inputs = List.map (typing_arg cenv) s.sig_inputs;
    sig_outputs = List.map (typing_arg cenv) s.sig_outputs; }

let program p =
  let program_desc pd = match pd with
    | Pnode n -> Pnode (node n)
    | Pconst c -> Pconst (typing_const_dec c)
    | Ptype t -> Ptype (typing_typedec t)
  in
  { p with p_desc = List.map program_desc p.p_desc }

let interface i =
  let interface_desc id = match id with
      | Iconstdef c -> Iconstdef (typing_const_dec c)
      | Itypedef t -> Itypedef (typing_typedec t)
      | Isignature i -> Isignature (typing_signature i)
  in
  { i with i_desc = List.map interface_desc i.i_desc }
