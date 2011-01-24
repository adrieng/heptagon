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
open Types
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



(** When not [partial],
      @raise Partial_evaluation when the application of the operator can't be evaluated (only Unknown_op).
    Otherwise keep as it is unknown operators. *)
let apply_op partial loc op se_list =
  match se_list with
    | [{ se_desc = Sint n1 }; { se_desc = Sint n2 }] ->
        (match op with
           | { qual = Pervasives; name = "+" } ->
               Sint (n1 + n2)
           | { qual = Pervasives; name = "-" } ->
               Sint (n1 - n2)
           | { qual = Pervasives; name = "*" } ->
               Sint (n1 * n2)
           | { qual = Pervasives; name = "/" } ->
               if n2 = 0 then raise (Evaluation_failed (Division_by_zero, loc));
               Sint (n1 / n2)
           | { qual = Pervasives; name = "=" } ->
               Sbool (n1 = n2)
           | _ -> assert false (*TODO: add missing operators*)
        )
    | [{ se_desc = Sint n }] ->
        (match op with
           | { qual = Pervasives; name = "~-" } -> Sint (-n)
           | _ -> assert false (*TODO: add missing operators*)
        )
    | _ -> if partial then Sop(op, se_list) (* partial evaluation *)
           else raise (Partial_evaluation (Unknown_op op, loc))


(** When not [partial],
      @raise Partial_evaluation when a static var cannot be evaluated, a local static parameter for example.
    Otherwise evaluate in a best effort manner. *)
let rec eval_core partial env se = match se.se_desc with
  | Sint _ | Sfloat _ | Sbool _ | Sconstructor _ | Sfield _ -> se
  | Svar ln ->
      (try (* first try to find in global const env *)
         let cd = find_const ln in
         eval_core partial env cd.c_value
       with Not_found -> (* then try to find in local env *)
         (try
            let se = QualEnv.find ln env in
            (match se.se_desc with
               | Svar ln' when ln'=ln -> (* prevent basic infinite loop *)
                  if partial then se else raise Not_found
               | _ -> eval_core partial env se
            )
          with Not_found -> (* Could not evaluate the var *)
            if partial then se
            else raise (Partial_evaluation (Unknown_param ln, se.se_loc))
         )
      )
  | Sop (op, se_list) ->
      let se_list = List.map (eval_core partial env) se_list in
      let se_desc = apply_op partial se.se_loc op se_list in
      { se with se_desc = se_desc }
  | Sarray se_list ->
      { se with se_desc = Sarray (List.map (eval_core partial env) se_list) }
  | Sarray_power (se, n) ->
       { se with se_desc = Sarray_power (eval_core partial env se, eval_core partial env n) }
  | Stuple se_list ->
       { se with se_desc = Stuple (List.map (eval_core partial env) se_list) }
  | Srecord f_se_list ->
      { se with se_desc = Srecord
          (List.map (fun (f,se) -> f, eval_core partial env se) f_se_list) }
  | Sasync se' ->
      { se with se_desc = Sasync (eval_core partial env se') }

(** [simplify env e] returns e simplified with the
    variables values taken from [env] or from the global env with [find_const].
    Every operator that can be computed is.
    It can return static_exp with uninstanciated variables.*)
let simplify env se =
  try eval_core true env se
  with exn -> message exn

(** [eval env e] does the same as [simplify]
    but if it returns, there are no variables nor op left.
    @raise [Errors.Error] when it cannot fully evaluate. *)
let eval env se =
  try eval_core false env se
  with exn -> message exn

(** [int_of_static_exp env e] returns the value of the expression
    [e] in the environment [env], mapping vars to integers.
    @raise [Errors.Error] if it cannot be computed.*)
let int_of_static_exp env se = match (eval env se).se_desc with
  | Sint i -> i
  | _ -> Misc.internal_error "static int_of_static_exp" 1

(** [is_true env constr] returns whether the constraint is satisfied
    in the environment (or None if this can be decided)
    and a simplified constraint. *)
let is_true env =
  function
    | Cequal (e1, e2) when e1 = e2 ->
        Some true, Cequal (simplify env e1, simplify env e2)
    | Cequal (e1, e2) ->
        let e1 = simplify env e1 in
       let e2 = simplify env e2 in
        (match e1.se_desc, e2.se_desc with
           | Sint n1, Sint n2 -> Some (n1 = n2), Cequal (e1, e2)
           | (_, _) -> None, Cequal (e1, e2))
    | Clequal (e1, e2) ->
        let e1 = simplify env e1 in
        let e2 = simplify env e2 in
        (match e1.se_desc, e2.se_desc with
           | Sint n1, Sint n2 -> Some (n1 <= n2), Clequal (e1, e2)
           | _, _ -> None, Clequal (e1, e2))
    | Cfalse -> None, Cfalse

exception Solve_failed of size_constraint

(** [solve env constr_list solves a list of constraints. It
    removes equations that can be decided and simplify others.
    If one equation cannot be satisfied, it raises Solve_failed. ]*)
let rec solve const_env =
  function
    | [] -> []
    | c :: l ->
        let l = solve const_env l in
        let (res, c) = is_true const_env c in
        (match res with
           | None -> c :: l
           | Some v -> if not v then raise (Solve_failed c) else l)

(** Substitutes variables in the size exp with their value
    in the map (mapping vars to size exps). *)
let rec static_exp_subst m se =
  match se.se_desc with
    | Svar qn -> (try QualEnv.find qn m with | Not_found -> se)
    | Sop (op, se_list) ->
        { se with se_desc = Sop (op, List.map (static_exp_subst m) se_list) }
    | Sarray_power (se, n) ->
        { se with se_desc = Sarray_power (static_exp_subst m se,
                                          static_exp_subst m n) }
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


