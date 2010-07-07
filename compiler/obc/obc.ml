(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* Object code internal representation *)

open Misc
open Names
open Ident
open Types

type var_name = ident
type type_name = longname
type fun_name = longname
type class_name = name
type instance_name = longname
type obj_name = name
type op_name = longname
type field_name = longname

type type_dec =
    { t_name : name;
      t_desc : tdesc }

and tdesc =
  | Type_abs
  | Type_enum of name list
  | Type_struct of (name * ty) list

type lhs = { l_desc : lhs_desc; l_ty : ty }

and lhs_desc =
  | Lvar of var_name
  | Lmem of var_name
  | Lfield of lhs * field_name
  | Larray of lhs * exp

and exp = { e_desc : exp_desc; e_ty : ty }

and exp_desc =
  | Elhs of lhs
  | Econst of static_exp
  | Eop of op_name * exp list
  | Estruct of type_name * (field_name * exp) list
  | Earray of exp list

type obj_call =
  | Oobj of obj_name
  | Oarray of obj_name * lhs

type method_name =
  | Mreset
  | Mstep
  | Mother of name

type act =
  | Aassgn of lhs * exp
  | Acall of lhs list * obj_call * method_name * exp list
  | Acase of exp * (longname * block) list
  | Afor of var_name * static_exp * static_exp * block

and block = act list

type var_dec =
    { v_ident : var_name;
      v_type : ty; (*v_controllable : bool*) }

type obj_dec =
    { o_name : obj_name;
      o_class : instance_name;
      o_size : static_exp; }

type method_def =
    { f_name : fun_name;
      f_inputs : var_dec list;
      f_outputs : var_dec list;
      f_locals : var_dec list;
      f_body : act list; }

type class_def =
    { c_name : class_name;
      c_mems : var_dec list;
      c_objs  : obj_dec list;
      c_methods: method_def list; }

type program =
    { p_pragmas: (name * string) list;
      p_opened : name list;
      p_types : type_dec list;
      p_defs  : class_def list }

let mk_var_dec name ty =
  { v_ident = name; v_type = ty }

let mk_exp ?(ty=invalid_type) desc =
  { e_desc = desc; e_ty = ty }

let mk_lhs ?(ty=invalid_type) desc =
  { l_desc = desc; l_ty = ty }

let rec var_name x =
  match x with
    | Lvar x -> x
    | Lmem x -> x
    | Lfield(x,_) -> var_name x
    | Larray(l, _) -> var_name l

(** Returns whether an object of name n belongs to
    a list of var_dec. *)
let rec vd_mem n = function
  | [] -> false
  | vd::l -> vd.v_ident = n or (vd_mem n l)

(** Returns the var_dec object corresponding to the name n
    in a list of var_dec. *)
let rec vd_find n = function
  | [] -> Format.printf "Not found var %s\n" (name n); raise Not_found
  | vd::l ->
      if vd.v_ident = n then vd else vd_find n l

let lhs_of_exp = function
  | Elhs l -> l
  | _ -> assert false
