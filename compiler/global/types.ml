(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Names
open Misc
open Location

type static_exp = { se_desc: static_exp_desc; se_ty: ty; se_loc: location }

and static_exp_desc =
  | Svar of constant_name
  | Sint of int
  | Sfloat of float
  | Sbool of bool
  | Sconstructor of constructor_name
  | Stuple of static_exp list
  | Sarray_power of static_exp * static_exp (** power : 0^n : [0,0,0,0,0,..] *)
  | Sarray of static_exp list (** [ e1, e2, e3 ] *)
  | Srecord of (field_name * static_exp) list (** { f1 = e1; f2 = e2; ... } *)
  | Sop of fun_name * static_exp list (** defined ops for now in pervasives *)

and ty = | Tprod of ty list | Tid of type_name | Tarray of ty * static_exp

let invalid_type = Tprod []

let prod = function
  | []      -> assert false
  | [ty]    -> ty
  | ty_list -> Tprod ty_list


(** DO NOT use this after the typing, since it could give invalid_type *)
let mk_static_exp ?(loc = no_location) ?(ty = invalid_type) desc =
  { se_desc = desc; se_ty = ty; se_loc = loc }


