(** This module defines static expressions, used in arrays definition and anywhere 
    a static value is expected. For instance:
    const n:int = 3;
    var x : int^n; var y : int^(n+2);
    x[n-1], x[1+3],...
*)
open Names
open Format

type op = SPlus | SMinus | STimes | SDiv

type size_exp =
  | SConst of int
  | SVar of name
  | SOp of op * size_exp * size_exp

(** Constraints on size expressions. *)
type size_constr =
  | Equal of size_exp * size_exp (* e1 = e2*)
  | LEqual of size_exp * size_exp (* e1 <= e2 *)
  | False (* unsatisfiable constraint *)

exception Instanciation_failed 
exception Not_static

(** Returns the op from an operator full name. *)
let op_from_app_name n =
  match n with
    | Modname({ qual = "Pervasives"; id = "+" }) | Name "+" -> SPlus
    | Modname({ qual = "Pervasives"; id = "-" }) | Name "-" -> SMinus
    | Modname({ qual = "Pervasives"; id = "*" }) | Name "*" -> STimes
    | Modname({ qual = "Pervasives"; id = "/" }) | Name "/" -> SDiv
    | _ -> raise Not_static

(** [simplify env e] returns e simplified with the
    variables values taken from env (mapping vars to integers).
    Variables are replaced with their values and every operator
    that can be computed is replaced with the value of the result. *)
let rec simplify env = function
  | SConst n -> SConst n
  | SVar id -> 
      (try 
	simplify env (NamesEnv.find id env) 
      with
	  _ -> SVar id
      )
  | SOp(op, e1, e2) ->
      let e1 = simplify env e1 in
      let e2 = simplify env e2 in
	(match e1, e2 with
	   | SConst n1, SConst n2 -> 
	       let n = (match op with
		  | SPlus -> n1 + n2
		  | SMinus -> n1 - n2
		  | STimes -> n1 * n2
		  | SDiv ->
		      if n2 = 0 then
			raise Instanciation_failed
		      else
			n1 / n2
	       ) in
		 SConst n
	   | _, _ -> SOp(op, e1, e2)
	)

(** [int_of_size_exp env e] returns the value of the expression
    [e] in the environment [env], mapping vars to integers. Raises
    Instanciation_failed if it cannot be computed (if a var has no value).*)
let int_of_size_exp env e =
  match simplify env e with
    | SConst n -> n
    | _ -> raise Instanciation_failed      

(** [is_true env constr] returns whether the constraint is satisfied
    in the environment (or None if this can be decided)
    and a simplified constraint. *)
let is_true env = function
  | Equal (e1,e2) when e1 = e2 -> 
      Some true, Equal (simplify env e1, simplify env e2)
  | Equal (e1, e2) ->
      let e1 = simplify env e1 in
      let e2 = simplify env e2 in
	(match e1, e2 with
	   | SConst n1, SConst n2 ->
	       Some (n1 = n2), Equal (e1,e2)
	   | _, _ -> None, Equal (e1,e2)
	)
  | LEqual (e1, e2) ->
      let e1 = simplify env e1 in
      let e2 = simplify env e2 in
	(match e1, e2 with
	   | SConst n1, SConst n2 ->
	       Some (n1 <= n2), LEqual (e1,e2)
	   | _, _ -> None, LEqual (e1,e2)
	)
  | False -> None, False

exception Solve_failed of size_constr
(** [solve env constr_list solves a list of constraints. It
    removes equations that can be decided and simplify others. 
    If one equation cannot be satisfied, it raises Solve_failed. ]*)
let rec solve const_env = function
  | [] -> []
  | c::l -> 
      let l = solve const_env l in
      let res, c = is_true const_env c in
	(match res with
	   | None -> c::l
	   | Some v -> if not v then raise (Solve_failed c) else l
	)

(** Substitutes variables in the size exp with their value
    in the map (mapping vars to size exps). *)
let rec size_exp_subst m = function
  | SVar n ->
      (try 
	List.assoc n m
      with 
	  Not_found -> SVar n
      )
  | SOp(op,e1,e2) -> SOp(op, size_exp_subst m e1, size_exp_subst m e2)
  | s -> s

(** Substitutes variables in the constraint list with their value
    in the map (mapping vars to size exps). *)
let instanciate_constr m constr =
  let replace_one m = function
    | Equal(e1,e2) -> Equal(size_exp_subst m e1, size_exp_subst m e2)
    | LEqual(e1,e2) -> LEqual(size_exp_subst m e1, size_exp_subst m e2)
  in
    List.map (replace_one m) constr 

let op_to_string = function
  | SPlus -> "+"
  | SMinus -> "-"
  | STimes -> "*"
  | SDiv -> "/"

let rec print_size_exp ff = function
  | SConst i -> fprintf ff "%d" i
  | SVar id -> fprintf ff "%s" id
  | SOp (op, e1, e2) ->
      fprintf ff "@[(";
      print_size_exp ff e1;
      fprintf ff " %s " (op_to_string op);
      print_size_exp ff e2;
      fprintf ff ")@]"

let rec print_list ff print sep l =
  match l with
    | [] -> ()
    | [x] -> print ff x
    | x :: l ->
        print ff x;
        fprintf ff "%s@ " sep;
        print_list ff print sep l

let print_size_constr ff = function
  | Equal (e1, e2) ->      
      fprintf ff "@[";
      print_size_exp ff e1;
      fprintf ff " = ";
      print_size_exp ff e2;
      fprintf ff "@]"
  | LEqual (e1, e2) ->      
      fprintf ff "@[";
      print_size_exp ff e1;
      fprintf ff " <= ";
      print_size_exp ff e2;
      fprintf ff "@]"
  | False ->
      fprintf ff "False"

let psize_constr oc c =
  let ff = formatter_of_out_channel oc in
    print_size_constr ff c; fprintf ff "@?"
