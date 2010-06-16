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

let const_array_of ty n = Tarray (ty, SConst n)
