(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Names


type ty = | Tprod of ty list | Tid of longname | Tarray of ty * static_exp

type static_exp = { se_desc: static_exp_desc; se_typ:  loc: location }
  | Svar of name
  | Sint of int
  | Sfloat of float
  | Sbool of bool
  | Sconstructor of longname
  | Stuple of static_exp list
  | Sarray_power of static_exp * static_exp (** power : 0^n : [0,0,0,0,0,..] *)
  | Sarray of static_exp list (** [ e1, e2, e3 ] *)
  | Sop of longname * static_exp list (** defined ops for now in pervasives *)

let invalid_type = Tprod []

let const_array_of ty n = Tarray (ty, SConst n) (* TODO ??? *)

open Pp_tools
open Format

let rec print_type ff = function
  | Tprod ty_list ->
      fprintf ff "@[<hov2>%a@]" (print_list_r print_type "(" " *" ")") ty_list
  | Tid id -> print_longname ff id
  | Tarray (ty, n) ->
      fprintf ff "@[<hov2>%a^%a@]" print_type ty print_static_exp n
