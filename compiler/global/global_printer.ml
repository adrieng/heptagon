open Names
open Signature
open Types
open Clocks
open Modules
open Format
open Pp_tools

let print_qualname ff qn = match qn with
  | { qual = "Pervasives"; name = n } -> print_name ff n
  | { qual = m; name = n } when m = g_env.current_mod -> print_name ff n
  | { qual = m; name = n } -> fprintf ff "%s.%a" m print_name n


let rec print_static_exp ff se = match se.se_desc with
  | Sint i -> fprintf ff "%d" i
  | Sbool b -> fprintf ff "%b" b
  | Sfloat f -> fprintf ff "%f" f
  | Sconstructor ln -> print_qualname ff ln
  | Svar id -> fprintf ff "%a" print_qualname id
  | Sop (op, se_list) ->
      if is_infix (shortname op)
      then
        let op_s = opname op ^ " " in
        fprintf ff "@[%a@]"
          (print_list_l print_static_exp "(" op_s ")") se_list
      else
        fprintf ff "@[<2>%a@,%a@]"
          print_qualname op  print_static_exp_tuple se_list
  | Sarray_power (se, n) ->
      fprintf ff "%a^%a" print_static_exp se  print_static_exp n
  | Sarray se_list ->
      fprintf ff "@[<2>%a@]" (print_list_r print_static_exp "["";""]") se_list
  | Stuple se_list -> print_static_exp_tuple ff se_list
  | Srecord f_se_list ->
      print_record (print_couple print_qualname
                      print_static_exp """ = """) ff f_se_list

and print_static_exp_tuple ff l =
  fprintf ff "@[<2>%a@]" (print_list_r print_static_exp "("","")") l

and print_type ff = function
  | Tprod ty_list ->
      fprintf ff "@[<hov2>%a@]" (print_list_r print_type "(" " *" ")") ty_list
  | Tid id -> print_qualname ff id
  | Tarray (ty, n) ->
      fprintf ff "@[<hov2>%a^%a@]" print_type ty print_static_exp n

let print_size_constraint ff = function
  | Cequal (e1, e2) ->
      fprintf ff "@[%a = %a@]" print_static_exp e1 print_static_exp e2
  | Clequal (e1, e2) ->
      fprintf ff "@[%a <= %a@]" print_static_exp e1 print_static_exp e2
  | Cfalse -> fprintf ff "Cfalse"

let print_param ff p =
  fprintf ff "%a:%a"  Names.print_name p.p_name  print_type p.p_type


