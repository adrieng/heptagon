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

type async_t = unit

type static_exp = { se_desc: static_exp_desc; se_ty: ty; se_loc: location }

and static_exp_desc =
  | Svar of constant_name
  | Sint of int
  | Sfloat of float
  | Sbool of bool
  | Sconstructor of constructor_name
  | Sfield of field_name
  | Stuple of static_exp list
  | Sarray_power of static_exp * static_exp (** power : 0^n : [0,0,0,0,0,..] *)
  | Sarray of static_exp list (** [ e1, e2, e3 ] *)
  | Srecord of (field_name * static_exp) list (** { f1 = e1; f2 = e2; ... } *)
  | Sop of fun_name * static_exp list (** defined ops for now in pervasives *)

and ty =
  | Tprod of ty list (** Product type used for tuples *)
  | Tid of type_name (** Usable type_name are alias or pervasives {bool,int,float} (see [Initial]) *)
  | Tarray of ty * static_exp (** [base_type] * [size] *)
  | Tasync of async_t * ty (** [async_annotation] * [base_type] *)
  | Tunit

let invalid_type = Tprod [] (** Invalid type given to untyped expression etc. *)

let prod = function
  | []      -> assert false
  | [ty]    -> ty
  | ty_list -> Tprod ty_list

let unprod = function
  | Tprod l -> l
  | t -> [t]


let asyncify async ty_list = match async with
  | None -> ty_list
  | Some a -> List.map (fun ty -> Tasync (a,ty)) ty_list


(** DO NOT use this after the typing, since it could give invalid_type *)
let mk_static_exp ?(loc = no_location) ?(ty = invalid_type) desc =
  { se_desc = desc; se_ty = ty; se_loc = loc }


