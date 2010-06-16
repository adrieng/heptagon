(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* The internal MiniLustre representation *)

open Location
open Dep
open Misc
open Names
open Ident
open Signature
open Static
open Types

type iterator_type = 
  | Imap
  | Ifold
  | Imapfold

type type_dec =
    { t_name: name;
      t_desc: tdesc;
      t_loc: location }

and tdesc =
  | Type_abs
  | Type_enum of name list
  | Type_struct of structure

and exp =
    { e_desc: edesc;        (* its descriptor *)
      mutable e_ck: ck;
      mutable e_ty: ty;
      e_loc: location }

and edesc =
  | Econst of const
  | Evar of ident
  | Econstvar of name
  | Efby of const option * exp
  | Etuple of exp list
  | Ecall of op_desc * exp list * ident option (** [op_desc] is the function called
                              [exp list] is the passed arguments
                              [ident option] is the optional reset condition *)

  | Ewhen of exp * longname * ident
  | Emerge of ident * (longname * exp) list
  | Eifthenelse of exp * exp * exp
  | Efield of exp * longname
  | Efield_update of longname * exp * exp (*field, record, value*)
  | Estruct of (longname * exp) list
  | Earray of exp list
  | Earray_op of array_op

and array_op =
  | Erepeat of size_exp * exp
  | Eselect of size_exp list * exp (*indices, array*)
  | Eselect_dyn of exp list * size_exp list * exp * exp (*indices, bounds, array, default*)
  | Eupdate of size_exp list * exp * exp (*indices, array, value*)
  | Eselect_slice of size_exp * size_exp * exp (*lower bound, upper bound, array*)
  | Econcat of exp * exp
  | Eiterator of iterator_type * longname * size_exp list * size_exp * exp list * ident option
   
and op_desc = { op_name: longname; op_params: size_exp list; op_kind: op_kind }
and op_kind = | Eop | Enode

and ct =
  | Ck of ck
  | Cprod of ct list

and ck =
  | Cbase
  | Cvar of link ref
  | Con of ck * longname * ident

and link =
  | Cindex of int
  | Clink of ck

and const =
  | Cint of int
  | Cfloat of float
  | Cconstr of longname
  | Carray of size_exp * const 

and pat =
  | Etuplepat of pat list
  | Evarpat of ident

type eq =
    { eq_lhs : pat;
      eq_rhs : exp;
      eq_loc : location }

type var_dec =
    { v_name : ident;
      v_type : ty;
      v_clock : ck }

type contract =
    { c_assume : exp;
      c_enforce : exp;
      c_controllables : var_dec list;
      c_local : var_dec list;
      c_eq : eq list;
    }

type node_dec =
    { n_name   : name;
      n_input  : var_dec list;
      n_output : var_dec list;
      n_contract : contract option;
      n_local  : var_dec list;
      n_equs   : eq list;
      n_loc    : location;
      n_params : param list; 
      n_params_constraints : size_constr list;
      n_params_instances : (int list) list; }(*TODO commenter ou passer en env*)

type const_dec =
    { c_name : name;
      c_value : size_exp;
      c_loc : location; }

type program =
    { p_pragmas: (name * string) list;
      p_opened : name list;
      p_types  : type_dec list;
      p_nodes  : node_dec list;
      p_consts : const_dec list; }



(*Helper functions to build the AST*)


let mk_exp ?(exp_ty = Tprod []) ?(clock = Cbase) ?(loc = no_location) desc =
  { e_desc = desc; e_ty = exp_ty; e_ck = clock; e_loc = loc }


let rec size_exp_of_exp e =
  match e.e_desc with 
  | Econstvar n -> SVar n
  | Econst (Cint i) -> SConst i
  | Ecall(op, [e1;e2], _) ->
      let sop = op_from_app_name op.op_name in
	    SOp(sop, size_exp_of_exp e1, size_exp_of_exp e2)
  | _ -> raise Not_static

(** @return the list of bounds of an array type*)
let rec bounds_list ty = 
  match ty with
    | Tarray(ty, n) -> n::(bounds_list ty)
    | _ -> []

(** @return the [var_dec] object corresponding to the name [n]
    in a list of [var_dec]. *)
let rec vd_find n = function
  | [] -> Format.printf "Not found var %s\n" (name n); raise Not_found
  | vd::l -> 
      if vd.v_name = n then vd else vd_find n l

(** @return whether an object of name [n] belongs to 
    a list of [var_dec]. *)
let rec vd_mem n = function
  | [] -> false
  | vd::l -> vd.v_name = n or (vd_mem n l)

(** @return whether [ty] corresponds to a record type. *)
let is_record_type ty = match ty with
  | Tid n ->
	    (try
	       ignore (Modules.find_struct n); true
	     with 
	     Not_found -> false)
  | _ -> false

(*
module Vars =
struct
  let rec vars_pat acc = function
    | Evarpat(x) -> x :: acc
    | Etuplepat(pat_list) -> List.fold_left vars_pat acc pat_list

  let rec vars_ck acc = function
    | Con(ck, c, n) -> if List.mem (IVar n) acc then acc else (IVar n) :: acc
    | Cbase | Cvar { contents = Cindex _ } -> acc
    | Cvar { contents = Clink ck }         -> vars_ck acc ck

  let rec read is_left acc e =
    let add x acc = if List.mem (IVar x) acc then acc else (IVar x) :: acc in
    let acc =
      match e.e_desc with
        | Emerge(x, c_e_list) ->
            let acc = add x acc in
            List.fold_left (fun acc (_, e) -> read is_left acc e) acc c_e_list
        | Eifthenelse(e1, e2, e3) ->
            read is_left (read is_left (read is_left acc e1) e2) e3
        | Ewhen(e, c, x) ->
            let acc = add x acc in
            read is_left acc e
        | Eop(_, _, e_list)
        | Etuple(e_list) -> List.fold_left (read is_left) acc e_list
        | Eapp(_, _, e_list) -> List.fold_left (read is_left) acc e_list
        | Eevery(_, _, e_list, x) ->
            let acc = add x acc in
              List.fold_left (read is_left) acc e_list
        | Efby(_, e) ->
            if is_left then vars_ck acc e.e_ck else read is_left acc e
	| Ereset_mem (_, _,res) -> add res acc
        | Evar(n) -> add n acc
	| Efield({ e_desc = Evar x }, f) -> 
	    let acc = add x acc in
	    let x = IField(x,f) in
	      if List.mem x acc then acc else x::acc
        | Efield(e, _) -> read is_left acc e
        | Estruct(f_e_list) ->
            List.fold_left (fun acc (_, e) -> read is_left acc e) acc f_e_list
        | Econst _ | Econstvar _ -> acc 
    (*Array operators*)
	| Earray e_list -> List.fold_left (read is_left) acc e_list
	| Erepeat (_,e) -> read is_left acc e
	| Eselect (_,e) -> read is_left acc e
	| Eselect_dyn (e_list, _, e1, e2) -> 
	    let acc = List.fold_left (read is_left) acc e_list in 
	      read is_left (read is_left acc e1) e2
	| Eupdate (_, e1, e2) | Efield_update (_, e1, e2) ->
	    read is_left (read is_left acc e1) e2 
	| Eselect_slice (_ , _, e) -> read is_left acc e
	| Econcat (e1, e2) ->
	    read is_left (read is_left acc e1) e2 
	| Eiterator (_, _, _, _, e_list, _) ->  
	    List.fold_left (read is_left) acc e_list
    in
      vars_ck acc e.e_ck

  let rec remove x = function
    | [] -> []
    | y :: l -> if x = y then l else y :: remove x l

  let def acc { eq_lhs = pat } = vars_pat acc pat

  let read is_left { eq_lhs = pat; eq_rhs = e } =
    match pat, e.e_desc with
      |  Evarpat(n), Efby(_, e1) ->
           if is_left
           then remove (IVar n) (read is_left [] e1)
           else read is_left [] e1
      | _ -> read is_left [] e

  let rec remove_records = function
    | [] -> []
    | (IVar x)::l -> (IVar x)::(remove_records l)
    | (IField(x,f))::l -> 
	let l = remove (IVar x) l in
	  (IField(x,f))::(remove_records l)

  let read_ivars is_left eq =
    remove_records (read is_left eq)

  let read is_left eq =
    filter_vars (read is_left eq)

  let antidep { eq_rhs = e } =
    match e.e_desc with Efby _ -> true | _ -> false
  let clock { eq_rhs = e } =
    match e.e_desc with
      | Emerge(_, (_, e) :: _) -> e.e_ck
      | _ -> e.e_ck
  let head ck =
    let rec headrec ck l =
      match ck with
        | Cbase | Cvar { contents = Cindex _ } -> l
        | Con(ck, c, n) -> headrec ck (n :: l)
        | Cvar { contents = Clink ck } -> headrec ck l in
    headrec ck []

  let rec linear_use acc e =
      match e.e_desc with
        | Emerge(_, c_e_list) ->
            List.fold_left (fun acc (_, e) -> linear_use acc e) acc c_e_list
        | Eifthenelse(e1, e2, e3) ->
            linear_use (linear_use (linear_use acc e1) e2) e3
        | Ewhen(e, _, _) | Efield(e, _) | Efby(_, e) -> linear_use acc e
        | Eop(_,_, e_list)
        | Etuple(e_list) | Earray e_list
        | Eapp(_,_, e_list) | Eiterator (_, _, _, _, e_list, _)
        | Eevery(_,_, e_list, _) -> List.fold_left linear_use acc e_list
        | Evar(n) ->
	    (match e.e_linearity with
	       | At _ -> if List.mem n acc then acc else n :: acc
	       | _ -> acc
	    )
        | Estruct(f_e_list) ->
            List.fold_left (fun acc (_, e) -> linear_use acc e) acc f_e_list
        | Econst _ | Econstvar _ | Ereset_mem (_, _,_) -> acc 
    (*Array operators*)
	| Erepeat (_,e)
	| Eselect (_,e) | Eselect_slice (_ , _, e) -> linear_use acc e
	| Eselect_dyn (e_list, _, e1, e2) -> 
	    let acc = List.fold_left linear_use acc e_list in 
	      linear_use (linear_use acc e1) e2
	| Eupdate (_, e1, e2) | Efield_update (_, e1, e2) 
	| Econcat (e1, e2) ->
	    linear_use (linear_use acc e1) e2 

  let mem_reset { eq_rhs = e } =
    match e.e_desc with
      | Ereset_mem (y, _, _) -> [y]
      | _ -> []
end
*)
(*
(* data-flow dependences. pre-dependences are discarded *)
module DataFlowDep = Make
  (struct
     type equation = eq
     let read eq = Vars.read true eq
     let def = Vars.def
     let linear_read eq = Vars.linear_use [] eq.eq_rhs
     let mem_reset = Vars.mem_reset
     let antidep = Vars.antidep
   end)

(* all dependences between variables *)
module AllDep = Make
  (struct
     type equation = eq
     let read eq = Vars.read false eq
     let linear_read eq = Vars.linear_use [] eq.eq_rhs
     let mem_reset = Vars.mem_reset
     let def = Vars.def
     let antidep eq = false
   end)
*)

