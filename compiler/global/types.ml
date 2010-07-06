(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
open Static
open Names

type ty =
  | Tprod of ty list | Tid of longname | Tarray of ty * size_exp

let invalid_type = Tprod []

let const_array_of ty n = Tarray (ty, Sconst n)

open Pp_tools
open Format

let rec print_type ff = function
  | Tprod ty_list ->
      fprintf ff "@[<hov2>%a@]" (print_list_r print_type "(" " *" ")") ty_list
  | Tid id -> print_longname ff id
  | Tarray (ty, n) ->
      fprintf ff "@[<hov2>%a^%a@]" print_type ty print_size_exp n
