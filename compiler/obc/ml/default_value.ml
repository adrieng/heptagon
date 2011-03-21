(**************************************************************************)
(*                                                                        *)
(*  Lucid Synchrone                                                       *)
(*                                                                        *)
(*  Author : Gregoire Hamon, Marc Pouzet                                  *)
(*  Organization : SPI team, LIP6 laboratory, University Paris 6          *)
(*                                                                        *)
(**************************************************************************)

(* $Id: default_value.ml,v 1.1.1.1 2005-11-03 15:45:23 pouzet Exp $ *)

(** Computes a default value from a type *)

open Misc
open Names
open Def_types
open Types
open Initialization
open Caml

let default x ty =
  let rec def ty =
    match ty with
      TypeVar{contents = Typindex _} -> Cdummy ""
    | TypeVar{contents = Typlink ty} -> def ty
    | Tarrow _ -> x
    | Tproduct(t_list) ->
        if t_list = []
        then Cdummy ""
        else Ctuple (List.map def t_list)
    | Tconstr (info, tlist) ->
  if info.qualid.qual = pervasives_module then
    match info.qualid.id with
      | "int" -> Cim (Cint 0)
      | "bool" | "clock" -> Cim (Cbool false)
      | "float" -> Cim (Cfloat 0.0)
      | "char" -> Cim (Cchar 'a')
      | "string" -> Cim (Cstring "")
      | "unit" -> Cim (Cvoid)
      | _ -> Cdummy ""
  else
    match info.info_in_table.type_desc with
      Abstract_type -> Cdummy ""
    | Variant_type l ->
        begin
    let case = List.hd l in
    match case.info_in_table.typ_desc with
      Tarrow (ty1, ty2) ->
        Cconstruct1 ({ cqual = case.qualid.qual;
           cid = case.qualid.id }, def ty1)
    |  _ ->
        Cconstruct0 { cqual = case.qualid.qual;
          cid = case.qualid.id }
        end
    | Record_type l ->
        let field_of_type x =
    let ty1,_ = filter_arrow x.info_in_table.typ_desc in
    ({ cqual = x.qualid.qual; cid = x.qualid.id }, def ty1) in
        Crecord (List.map field_of_type l)
  in
  def ty


