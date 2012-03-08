(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(** This module defines static expressions, used in params and for constants.
    const n: int = 3;
    var x : int^n; var y : int^(n + 2);
    x[n - 1], x[1 + 3],... *)

open Names
open Format
open Signature
open Signature
open Modules
open Location


exception Not_static



(** Some evaluations are not possible *)
type eval_error = Division_by_zero
exception Evaluation_failed of eval_error * location

(** Some unknown operators could be used preventing the evaluation *)
type partial_eval_cause = Unknown_op of fun_name | Unknown_param of qualname
exception Partial_evaluation of partial_eval_cause * location

let message exn =
  begin match exn with
    | Evaluation_failed (e,loc) ->
        (match e with
          | Division_by_zero ->
              eprintf "%aForbidden division by 0.@."
              print_location loc
        )
    | Partial_evaluation (e,loc) ->
        (match e with
          | Unknown_op op ->
              eprintf "%aUnknown operator %a.@."
              Location.print_location loc
              Global_printer.print_qualname op
          | Unknown_param q ->
              eprintf "%aUninstanciated param %a.@."
              Location.print_location loc
              Global_printer.print_qualname q
        )
    | _ -> raise exn
  end;
  raise Errors.Error



let funs_apply_subst env =
  let stexp_desc funs () = function
    | Svar ln ->
      begin try
        let se = QualEnv.find ln env in
        se.se_desc, ()
      with Not_found -> raise Errors.Fallback end
    | _ -> raise Errors.Fallback
  in
  { Global_mapfold.defaults with Global_mapfold.static_exp_desc = stexp_desc }

(** [apply_subst_se env se] apply the substitution given by env to se. *)
let apply_subst_se env se =
  let se, _ = Global_mapfold.static_exp_it (funs_apply_subst env) () se in
  se

(** [apply_subst_ty env t] apply the substitution given by env to t. *)
let apply_subst_ty env t =
  let t, _ = Global_mapfold.ty_it (funs_apply_subst env) () t in
  t


(** When not [partial],
      @raise Partial_evaluation when the application of the operator can't be evaluated.
    Otherwise keep as it is unknown operators. *)
let apply_op partial loc op se_list =
  let has_var_desc acc se =
    let has_var _ _ sed = match sed with
      | Svar _ -> sed,true
      | _ -> raise Errors.Fallback
    in
    let se, acc =
      Global_mapfold.static_exp_it
        {Global_mapfold.defaults with Global_mapfold.static_exp_desc = has_var}
        acc se
    in
    se.se_desc, acc
  in
  let sed_l, has_var = Misc.mapfold has_var_desc false se_list in
  if (op.qual = Pervasives) && not has_var
  then ( (* concrete evaluation *)
    match op.name, sed_l with
      | "+", [Sint n1; Sint n2] -> Sint (Int32.add n1 n2)
      | "-", [Sint n1; Sint n2] -> Sint (Int32.sub n1 n2)
      | "*", [Sint n1; Sint n2] -> Sint (Int32.mul n1 n2)
      | "/", [Sint n1; Sint n2] ->
          if n2 = 0l then raise (Evaluation_failed (Division_by_zero, loc));
          Sint (Int32.div n1 n2)
      | "+.", [Sfloat f1; Sfloat f2] -> Sfloat (f1 +. f2)
      | "-.", [Sfloat f1; Sfloat f2] -> Sfloat (f1 -. f2)
      | "*.", [Sfloat f1; Sfloat f2] -> Sfloat (f1 *. f2)
      | "/.", [Sfloat f1; Sfloat f2] ->
          if f2 = 0.0 then raise (Evaluation_failed (Division_by_zero, loc));
          Sfloat (f1 /. f2)
      | "=", [Sint n1; Sint n2] -> Sbool (n1 = n2)
      | "<=", [Sint n1; Sint n2] -> Sbool (n1 <= n2)
      | ">=", [Sint n1; Sint n2] -> Sbool (n1 >= n2)
      | "<", [Sint n1; Sint n2] -> Sbool (n1 < n2)
      | ">", [Sint n1; Sint n2] -> Sbool (n1 > n2)
      | ">>>", [Sint n1; Sint n2] -> Sint (Int32.shift_right n1 (Int32.to_int n2))
      | "<<<", [Sint n1; Sint n2] -> Sint (Int32.shift_left n1 (Int32.to_int n2))
      | "&", [Sbool b1; Sbool b2] -> Sbool (b1 && b2)
      | "or", [Sbool b1; Sbool b2] -> Sbool (b1 || b2)
      | "not", [Sbool b] -> Sbool (not b)
      | "~-", [Sint n] -> Sint (Int32.neg n)
      | "~~", [Sint n] -> Sint (Int32.lognot n)
      | "~-.", [Sfloat f] -> Sfloat (-. f)
      | "&&&", [Sint n1; Sint n2] -> Sint (Int32.logand n1 n2)
      | "|||", [Sint n1; Sint n2] -> Sint (Int32.logor n1 n2)
      | "%", [Sint n1; Sint n2] -> Sint (Int32.rem n1 n2)
      | f,_ -> Misc.internal_error ("Static evaluation failed of the pervasive operator "^f)
  )
  else ( (* symbolic evaluation *)
    match op, sed_l with
      | {qual = Pervasives; name = "=" }, [sed1;sed2]
          when Global_compare.static_exp_desc_compare sed1 sed2 = 0 -> Sbool true
      | _ ->
          if partial
          then Sop(op, se_list) (* partial evaluation *)
          else raise (Partial_evaluation (Unknown_op op, loc))
  )



(** When not [partial],
      @raise Partial_evaluation when a static var cannot be evaluated,
      a local static parameter for example.
    Otherwise evaluate in a best effort manner. *)
let rec eval_core partial se =
  let stexp_desc funs loc = function
    | Svar ({qual = LocalModule _} as ln) ->
        if partial
        then raise Errors.Fallback
        else raise (Partial_evaluation (Unknown_param ln, se.se_loc))
    | Svar ln ->
        (try (* try to find in global const env *)
           let cd = find_const ln in
           let se, _ = Global_mapfold.static_exp_it funs loc cd.c_value in
           se.se_desc, loc
         with Not_found -> (* Could not evaluate the var *)
           if partial
           then raise Errors.Fallback
           else raise (Partial_evaluation (Unknown_param ln, se.se_loc))
         )
    | Sop (op, se_l) ->
        let se_l, _ = Misc.mapfold (Global_mapfold.static_exp_it funs) loc se_l in
        apply_op partial loc op se_l, loc
    | _ -> raise Errors.Fallback
  in
  let static_exp funs _ se = Global_mapfold.static_exp funs se.se_loc se in
  let funs = { Global_mapfold.defaults with
               Global_mapfold.static_exp_desc = stexp_desc;
               Global_mapfold.static_exp = static_exp }
  in
  let se, _ = Global_mapfold.static_exp_it funs se.se_loc se in
  se


(** [simplify e] returns e simplified
    Every operator that can be computed is.
    It can return static_exp with uninstanciated variables.*)
let simplify se =
  try eval_core true se
  with exn -> message exn

(** [eval env e] evaluate a static expression with the
    variable values taken from [env] and the global env.
    If it returns, there are no variable nor op left.
    @raise [Errors.Error] when it cannot fully evaluate. *)
let eval se =
  try eval_core false se
  with exn -> message exn



(** [int_of_static_exp e] returns the value of the expression [e].
    @raise [Errors.Error] if it cannot be computed.*)
let int_of_static_exp se = match (eval se).se_desc with
  | Sint i -> i
  | _ -> Misc.internal_error "static int_of_static_exp"

(** [is_true constr] returns whether the constraint is satisfied,
    or None if this can be decided and a simplified constraint. *)
let is_true c =
  let c = simplify c in
  match c.se_desc with
    | Sbool b -> Some b, c
    | _ -> None, c

exception Solve_failed of constrnt

(** [solve constr_list solves a list of constraints. It
    removes equations that can be decided and simplify others.
    If one equation cannot be satisfied, it raises Solve_failed. ]*)
let rec solve =
  function
    | [] -> []
    | c :: l ->
        let l = solve l in
        let (res, solved_c) = is_true c in
        (match res with
           | None -> solved_c :: l
           | Some v -> if not v then raise (Solve_failed c) else l)
(*
(** Substitutes variables in the size exp with their value
    in the map (mapping vars to size exps). *)
let rec static_exp_subst m se =
  match se.se_desc with
    | Svar qn -> (try QualEnv.find qn m with | Not_found -> se)
    | Sop (op, se_list) ->
        { se with se_desc = Sop (op, List.map (static_exp_subst m) se_list) }
    | Sarray_power (se, n_list) ->
        { se with se_desc = Sarray_power (static_exp_subst m se,
                                          List.map (static_exp_subst m) n_list) }
    | Sarray se_list ->
        { se with se_desc = Sarray (List.map (static_exp_subst m) se_list) }
    | Stuple se_list ->
        { se with se_desc = Stuple (List.map (static_exp_subst m) se_list) }
    | Srecord f_se_list ->
        { se with se_desc =
            Srecord (List.map
                       (fun (f,se) -> f, static_exp_subst m se) f_se_list) }
    | _ -> se

(** Substitutes variables in the constraint list with their value
    in the map (mapping vars to size exps). *)
let instanciate_constr m constr =
  let replace_one m = function
    | Cequal (e1, e2) -> Cequal (static_exp_subst m e1, static_exp_subst m e2)
    | Clequal (e1, e2) -> Clequal (static_exp_subst m e1, static_exp_subst m e2)
    | Cfalse -> Cfalse in
  List.map (replace_one m) constr
*)

