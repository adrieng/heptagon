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

type op = | Splus | Sminus | Stimes | Sdiv

type size_exp =
  | SConst of int | Svar of name | Sop of op * size_exp * size_exp

(** Constraints on size expressions. *)
type size_constraint =
  | Cequal of size_exp * size_exp (* e1 = e2*)
  | Clequal of size_exp * size_exp (* e1 <= e2 *)
  | Cfalse

(* unsatisfiable constraint *)
exception Instanciation_failed

exception Not_static

(** Returns the op from an operator full name. *)
let op_from_app_name n =
  match n with
    | Modname { qual = "Pervasives"; id = "+" } | Name "+" -> Splus
    | Modname { qual = "Pervasives"; id = "-" } | Name "-" -> Sminus
    | Modname { qual = "Pervasives"; id = "*" } | Name "*" -> Stimes
    | Modname { qual = "Pervasives"; id = "/" } | Name "/" -> Sdiv
    | _ -> raise Not_static

(** [simplify env e] returns e simplified with the
    variables values taken from env (mapping vars to integers).
    Variables are replaced with their values and every operator
    that can be computed is replaced with the value of the result. *)
let rec simplify env =
  function
    | SConst n -> SConst n
    | Svar id -> (try simplify env (NamesEnv.find id env) with | _ -> Svar id)
    | Sop (op, e1, e2) ->
        let e1 = simplify env e1 in
        let e2 = simplify env e2
        in
        (match (e1, e2) with
           | (SConst n1, SConst n2) ->
               let n =
                 (match op with
                    | Splus -> n1 + n2
                    | Sminus -> n1 - n2
                    | Stimes -> n1 * n2
                    | Sdiv ->
                        if n2 = 0 then raise Instanciation_failed else n1 / n2)
               in SConst n
           | (_, _) -> Sop (op, e1, e2))

(** [int_of_size_exp env e] returns the value of the expression
    [e] in the environment [env], mapping vars to integers. Raises
    Instanciation_failed if it cannot be computed (if a var has no value).*)
let int_of_size_exp env e =
  match simplify env e with | SConst n -> n | _ -> raise Instanciation_failed

(** [is_true env constr] returns whether the constraint is satisfied
    in the environment (or None if this can be decided)

    and a simplified constraint. *)
let is_true env =
  function
    | Cequal (e1, e2) when e1 = e2 ->
        ((Some true), (Cequal (simplify env e1, simplify env e2)))
    | Cequal (e1, e2) ->
        let e1 = simplify env e1 in
        let e2 = simplify env e2
        in
        (match (e1, e2) with
           | (SConst n1, SConst n2) -> ((Some (n1 = n2)), (Cequal (e1, e2)))
           | (_, _) -> (None, (Cequal (e1, e2))))
    | Clequal (e1, e2) ->
        let e1 = simplify env e1 in
        let e2 = simplify env e2
        in
        (match (e1, e2) with
           | (SConst n1, SConst n2) -> ((Some (n1 <= n2)), (Clequal (e1, e2)))
           | (_, _) -> (None, (Clequal (e1, e2))))
    | Cfalse -> (None, Cfalse)

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
let rec size_exp_subst m =
  function
    | Svar n -> (try List.assoc n m with | Not_found -> Svar n)
    | Sop (op, e1, e2) -> Sop (op, size_exp_subst m e1, size_exp_subst m e2)
    | s -> s

(** Substitutes variables in the constraint list with their value
    in the map (mapping vars to size exps). *)
let instanciate_constr m constr =
  let replace_one m = function
      | Cequal (e1, e2) -> Cequal (size_exp_subst m e1, size_exp_subst m e2)
      | Clequal (e1, e2) -> Clequal (size_exp_subst m e1, size_exp_subst m e2)
      | Cfalse -> Cfalse
  in List.map (replace_one m) constr

let op_to_string =
  function | Splus -> "+" | Sminus -> "-" | Stimes -> "*" | Sdiv -> "/"

let rec print_size_exp ff =
  function
    | SConst i -> fprintf ff "%d" i
    | Svar id -> fprintf ff "%s" id
    | Sop (op, e1, e2) ->
        fprintf ff "@[(%a %s %a)@]"
          print_size_exp e1 (op_to_string op) print_size_exp e2

let print_size_constraint ff = function
  | Cequal (e1, e2) ->
      fprintf ff "@[%a = %a@]" print_size_exp e1 print_size_exp e2
  | Clequal (e1, e2) ->
      fprintf ff "@[%a <= %a@]" print_size_exp e1 print_size_exp e2
  | Cfalse -> fprintf ff "False"

let psize_constraint oc c =
  let ff = formatter_of_out_channel oc
  in (print_size_constraint ff c; fprintf ff "@?")

