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

let mk_static_exp ?(loc = no_location) ?(ty = invalid_type) desc =
  { se_desc = desc; se_ty = ty; se_loc = loc }


(**Iterators*)

type 'a types_it_funs = {
  static_exp : 'a types_it_funs -> 'a -> static_exp -> static_exp * 'a;
  static_exp_desc :
    'a types_it_funs -> 'a -> static_exp_desc -> static_exp_desc * 'a;
  ty : 'a types_it_funs -> 'a -> ty -> ty * 'a }

let rec static_exp_it funs acc se = funs.static_exp funs acc se
and static_exp funs acc se =
  let se_desc, acc = static_exp_desc_it funs acc se.se_desc in
  let se_ty, acc = ty_it funs acc se.se_ty in
  { se with se_desc = se_desc; se_ty = se_ty }, acc

and static_exp_desc_it funs acc sd =
  try funs.static_exp_desc funs acc sd
  with Fallback -> static_exp_desc funs acc sd

and static_exp_desc funs acc sd = match sd with
  | Svar _ | Sint _ | Sfloat _ | Sbool _ | Sconstructor _ -> sd, acc
  | Stuple se_l ->
      let se_l, acc = mapfold (static_exp_it funs) acc se_l in
      Stuple se_l, acc
  | Sarray se_l ->
      let se_l, acc = mapfold (static_exp_it funs) acc se_l in
      Sarray se_l, acc
  | Sop (n, se_l) ->
      let se_l, acc = mapfold (static_exp_it funs) acc se_l in
      Sop (n, se_l), acc
  | Sarray_power (se1, se2) ->
      let se1, acc = static_exp_it funs acc se1 in
      let se2, acc = static_exp_it funs acc se2 in
      Sarray_power(se1, se2), acc
  | Srecord f_se_l ->
      let aux acc (f,se) = let se,acc = static_exp_it funs acc se in
        (f, se), acc in
      let f_se_l, acc = mapfold aux acc f_se_l in
      Srecord f_se_l, acc

and ty_it funs acc t = try funs.ty funs acc t with Fallback -> ty funs acc t
and ty funs acc t = match t with
  | Tid _ -> t, acc
  | Tprod t_l -> let t_l, acc = mapfold (ty_it funs) acc t_l in Tprod t_l, acc
  | Tarray (t, se) ->
      let t, acc = ty_it funs acc t in
      let se, acc = static_exp_it funs acc se in
      Tarray (t, se), acc

let types_funs_default = {
  static_exp = static_exp;
  static_exp_desc = static_exp_desc;
  ty = ty }

open Pp_tools
open Format

let rec print_static_exp ff se = match se.se_desc with
  | Sint i -> fprintf ff "%d" i
  | Sbool b -> fprintf ff "%b" b
  | Sfloat f -> fprintf ff "%f" f
  | Sconstructor ln -> print_longname ff ln
  | Svar id -> fprintf ff "%a" print_longname id
  | Sop (op, se_list) ->
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
