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

type var_name = ident
type type_name = longname
type fun_name = longname
type class_name = name
type instance_name = longname
type obj_name = name
type op_name = longname
type field_name = longname

type ty =
  | Tint
  | Tfloat
  | Tbool
  | Tid of type_name
  | Tarray of ty * static_exp

type type_dec =
    { t_name : name;
      t_desc : tdesc }

and tdesc =
  | Type_abs
  | Type_enum of name list
  | Type_struct of (name * ty) list

type lhs =
  | Var of var_name
  | Mem of var_name
  | Field of lhs * field_name
  | Array of lhs * exp

and exp =
  | Lhs of lhs
  | Const of static_exp
  | Op of op_name * exp list
  | Struct_lit of type_name * (field_name * exp) list
  | Array_lit of exp list

type obj_call =
  | Context of obj_name
  | Array_context of obj_name * lhs

(* act list au lieu de Comp *)
type act =
  | Assgn of lhs * exp
  | Call of lhs list * obj_call * exp list
  | Case of exp * (longname * act list) list
  | For of var_name * static_exp * static_exp * act list
  | Reinit of obj_name

type var_dec =
    { v_ident : var_name;
      v_type : ty;
      (*v_controllable : bool*) }

type obj_dec =
    { o_name : obj_name;
      o_method : fun_name;
      o_class : instance_name;
      o_size : int; }

type method_def =
    { f_name : fun_name;
      f_inputs : var_dec list;
      f_outputs : var_dec list;
      f_locals : var_dec list;
      f_body : act list }

type class_def =
    { c_name : class_name;
      c_mems : var_dec list;
      c_objs  : obj_dec list;
      c_methods: method_def list; (*Map ?*) }

type program =
    { p_pragmas: (name * string) list;
      p_opened : name list;
      p_types : type_dec list;
      p_defs  : class_def list }

(*
type step_fun =
    { inp    : var_dec list;
      out    : var_dec list;
      local  : var_dec list;
      controllables : var_dec list; (* GD : ugly patch to delay controllable
                                       variables definition to target code
                                       generation *)
      bd     : act }

type reset_fun = act
    *)

let mk_var_dec name ty =
  { v_ident = name; v_type = ty }

let rec var_name x =
  match x with
    | Var x -> x
    | Mem x -> x
    | Field(x,_) -> var_name x
    | Array(l, _) -> var_name l

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
  | Lhs l -> l
  | _ -> assert false
