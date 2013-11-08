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

(** This module defines static expressions, used in params and for constants.
    [const n: int = 3;
     var x : int^n; var y : int^(n + 2); x[n - 1], x[1 + 3],...] *)

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
      | "+", [Sint n1; Sint n2] -> Sint (n1 + n2)
      | "-", [Sint n1; Sint n2] -> Sint (n1 - n2)
      | "*", [Sint n1; Sint n2] -> Sint (n1 * n2)
      | "/", [Sint n1; Sint n2] ->
          if n2 = 0 then raise (Evaluation_failed (Division_by_zero, loc));
          Sint (n1 / n2)
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
      | ">>>", [Sint n1; Sint n2] -> Sint (n1 lsr n2)
      | "<<<", [Sint n1; Sint n2] -> Sint (n1 lsl n2)
      | "&", [Sbool b1; Sbool b2] -> Sbool (b1 && b2)
      | "or", [Sbool b1; Sbool b2] -> Sbool (b1 || b2)
      | "not", [Sbool b] -> Sbool (not b)
      | "~-", [Sint n] -> Sint (-n)
      | "~~", [Sint n] -> Sint (lnot n)
      | "~-.", [Sfloat f] -> Sfloat (-. f)
      | "&&&", [Sint n1; Sint n2] -> Sint (n1 land n2)
      | "|||", [Sint n1; Sint n2] -> Sint (n1 lor n2)
      | "%", [Sint n1; Sint n2] -> Sint (n1 mod n2)
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
let rec eval_core partial env se = match se.se_desc with
  | Sint _ | Sfloat _ | Sbool _ | Sstring _ | Sconstructor _ | Sfield _ -> se
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
  | Sarray_power (se, n_list) ->
       { se with se_desc =
            Sarray_power (eval_core partial env se, List.map (eval_core partial env) n_list) }
  | Stuple se_list ->
       { se with se_desc = Stuple (List.map (eval_core partial env) se_list) }
  | Srecord f_se_list ->
      { se with se_desc = Srecord
          (List.map (fun (f,se) -> f, eval_core partial env se) f_se_list) }


(** [simplify env e] returns e simplified with the
    variables values taken from [env] or from the global env with [find_const].
    Every operator that can be computed is.
    It can return static_exp with uninstanciated variables.*)
let simplify env se =
  try eval_core true env se
  with exn -> message exn

let rec simplify_type env ty = match ty with
  | Tarray(ty, e) -> Tarray(simplify_type env ty, simplify env e)
  | Tprod l -> Tprod (List.map (simplify_type env) l)
  | t -> t

(** [eval env e] does the same as [simplify]
    but if it returns, there are no variables nor op left.
    @raise Errors.Error when it cannot fully evaluate. *)
let eval env se =
  try eval_core false env se
  with exn -> message exn

(** [int_of_static_exp env e] returns the value of the expression
    [e] in the environment [env], mapping vars to integers.
    @raise Errors.Error if it cannot be computed.*)
let int_of_static_exp env se = match (eval env se).se_desc with
  | Sint i -> i
  | _ -> Misc.internal_error "static int_of_static_exp"

(** [is_true env constr] returns whether the constraint is satisfied
    in the environment (or None if this can be decided)
    and a simplified constraint. *)
let is_true env c =
  let c = simplify env c in
  match c.se_desc with
    | Sbool b -> Some b, c
    | _ -> None, c

exception Solve_failed of constrnt

(** [solve env constr_list solves a list of constraints. It
    removes equations that can be decided and simplify others.
    If one equation cannot be satisfied, it raises Solve_failed. ]*)
let rec solve const_env =
  function
    | [] -> []
    | c :: l ->
        let l = solve const_env l in
        let (res, solved_c) = is_true const_env c in
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
