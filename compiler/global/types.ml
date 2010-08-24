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


open Pp_tools
open Format

let rec print_static_exp ff se = match se.se_desc with
  | Sint i -> fprintf ff "%d" i
  | Sbool b -> fprintf ff "%b" b
  | Sfloat f -> fprintf ff "%f" f
  | Sconstructor ln -> print_longname ff ln
  | Svar id -> fprintf ff "%a" print_longname id
  (* | Sop (op, [e_l; e_r]) -> *)
  (*     fprintf ff "(@[<2>%a@ %a %a@])" *)
  (*       print_static_exp e_l print_longname op print_static_exp r *)
  | Sop (op, se_list) ->
      if is_infix (shortname op)
      then
        let op_s = opname op ^ " " in
        fprintf ff "@[%a@]"
          (print_list_l print_static_exp "(" op_s ")") se_list
      else
        fprintf ff "@[<2>%a@,%a@]"
          print_longname op  print_static_exp_tuple se_list
  | Sarray_power (se, n) ->
      fprintf ff "%a^%a" print_static_exp se  print_static_exp n
  | Sarray se_list ->
      fprintf ff "@[<2>%a@]" (print_list_r print_static_exp "["";""]") se_list
  | Stuple se_list -> print_static_exp_tuple ff se_list
  | Srecord f_se_list ->
      print_record (print_couple print_longname
                      print_static_exp """ = """) ff f_se_list

and print_static_exp_tuple ff l =
  fprintf ff "@[<2>%a@]" (print_list_r print_static_exp "("","")") l

and print_type ff = function
  | Tprod ty_list ->
      fprintf ff "@[<hov2>%a@]" (print_list_r print_type "(" " *" ")") ty_list
  | Tid id -> print_longname ff id
  | Tarray (ty, n) ->
      fprintf ff "@[<hov2>%a^%a@]" print_type ty print_static_exp n
