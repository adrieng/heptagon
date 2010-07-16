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
    x[n - 1], x[1 + 3],...
*)

open Names
open Format
open Types
open Signature
open Modules

(* unsatisfiable constraint *)
exception Instanciation_failed

exception Not_static

(** Returns the op from an operator full name. *)
let op_from_app_name ln =
  match ln with
    | Modname { qual = "Pervasives" } -> ln
    | _ -> raise Not_static

(** [simplify env e] returns e simplified with the
    variables values taken from env (mapping vars to integers).
    Variables are replaced with their values and every operator
    that can be computed is replaced with the value of the result. *)
let rec simplify env se =
  match se.se_desc with
    | Sint _ | Sfloat _ | Sbool _ | Sconstructor _ -> se
    | Svar ln ->
        (try
           let { info = cd } = find_const ln in
             simplify env cd.c_value
         with
             Not_found ->
               (match ln with
                  | Name n -> (try simplify env (NamesEnv.find n env) with | _ -> se)
                  | Modname _ -> se)
        )
    | Sop (op, se_list) ->
        let se_list = List.map (simplify env) se_list in
          { se with se_desc = apply_op op se_list }
    | Sarray se_list ->
        { se with se_desc = Sarray (List.map (simplify env) se_list) }
    | Sarray_power (se, n) ->
         { se with se_desc = Sarray_power (simplify env se, simplify env n) }
    | Stuple se_list ->
         { se with se_desc = Stuple (List.map (simplify env) se_list) }
    | Srecord f_se_list ->
        { se with se_desc = Srecord
            (List.map (fun (f,se) -> f, simplify env se) f_se_list) }

and apply_op op se_list =
  match se_list with
    | [{ se_desc = Sint n1 }; { se_desc = Sint n2 }] ->
        (match op with
           | Modname { qual = "Pervasives"; id = "+" } ->
               Sint (n1 + n2)
           | Modname { qual = "Pervasives"; id = "-" } ->
               Sint (n1 - n2)
           | Modname { qual = "Pervasives"; id = "*" } ->
               Sint (n1 * n2)
           | Modname { qual = "Pervasives"; id = "/" } ->
               let n = if n2 = 0 then raise Instanciation_failed else n1 / n2 in
                 Sint n
           | _ -> assert false (*TODO: add missing operators*)
        )
    | [{ se_desc = Sint n }] ->
        (match op with
           | Modname { qual = "Pervasives"; id = "~-" } -> Sint (-n)
           | _ -> assert false (*TODO: add missing operators*)
        )
    | _ -> Sop(op, se_list)

(** [int_of_static_exp env e] returns the value of the expression
    [e] in the environment [env], mapping vars to integers. Raises
    Instanciation_failed if it cannot be computed (if a var has no value).*)
let int_of_static_exp env e =
  let e =  simplify env e in
  match e.se_desc with | Sint n -> n | _ -> raise Instanciation_failed

(** [is_true env constr] returns whether the constraint is satisfied
    in the environment (or None if this can be decided)
    and a simplified constraint. *)
let is_true env =
  function
    | Cequal (e1, e2) when e1 = e2 ->
        Some true, Cequal (simplify env e1, simplify env e2)
    | Cequal (e1, e2) ->
        let e1 = simplify env e1 in
        let e2 = simplify env e2
        in
        (match e1.se_desc, e2.se_desc with
           | Sint n1, Sint n2 -> Some (n1 = n2), Cequal (e1, e2)
           | (_, _) -> None, Cequal (e1, e2))
    | Clequal (e1, e2) ->
        let e1 = simplify env e1 in
        let e2 = simplify env e2
        in
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
        let (res, c) = is_true const_env c
        in
        (match res with
           | None -> c :: l
           | Some v -> if not v then raise (Solve_failed c) else l)

(** Substitutes variables in the size exp with their value
    in the map (mapping vars to size exps). *)
let rec static_exp_subst m se =
  match se.se_desc with
    | Svar ln ->
        (match ln with
           | Name n -> (try NamesEnv.find n m with | Not_found -> se)
           | Modname _ -> se)
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
    | Cfalse -> Cfalse
  in List.map (replace_one m) constr


open Format

let print_size_constraint ff = function
  | Cequal (e1, e2) ->
      fprintf ff "@[%a = %a@]" print_static_exp e1 print_static_exp e2
  | Clequal (e1, e2) ->
      fprintf ff "@[%a <= %a@]" print_static_exp e1 print_static_exp e2
  | Cfalse -> fprintf ff "Cfalse"

let psize_constraint oc c =
  let ff = formatter_of_out_channel oc
  in (print_size_constraint ff c; fprintf ff "@?")

