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
  | Tarray of ty * int

type type_dec =
    { t_name : name;
      t_desc : tdesc }

and tdesc =
  | Type_abs
  | Type_enum of name list
  | Type_struct of (name * ty) list

type const =
  | Cint of int
  | Cbool of bool
  | Cfloat of float
  | Cconstr of longname
  | Carray_power of int * const
  | Carray of const list
  | Ctuple of const list

type lhs =
  | Var of var_name
  | Mem of var_name
  | Field of lhs * field_name
  | Array of lhs * exp

and exp =
  | Lhs of lhs
  | Const of const
  | Op of op_name * exp list
  | Struct_lit of type_name * (field_name * exp) list
  | Array_lit of exp list

type obj_call =
  | Context of obj_name
  | Array_context of obj_name * lhs

type act =
  | Assgn of lhs * exp
  | Step_ap of lhs list * obj_call * exp list
  | Comp of act * act
  | Case of exp * (longname * act) list
  | For of var_name * int * int * act
  | Reinit of obj_name
  | Nothing

type var_dec =
    { v_ident : var_name;
      v_type : ty; }

type obj_dec =
    { obj : obj_name;
      cls : instance_name;
      size : int; }

type step_fun =
    { inp    : var_dec list;
      out    : var_dec list;
      local  : var_dec list;
      controllables : var_dec list; (* GD : ugly patch to delay controllable
                                       variables definition to target code
                                       generation *)
      bd     : act }

type reset_fun = act

type class_def =
    { cl_id : class_name;
      mem   : var_dec list;
      objs  : obj_dec list;
      reset : reset_fun;
      step  : step_fun; }

type program =
    { o_pragmas: (name * string) list;
      o_opened : name list;
      o_types : type_dec list;
      o_defs  : class_def list }

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
