(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* global data in the symbol tables *)
open Names
open Types
open Linearity

(** Warning: Whenever these types are modified,
    interface_format_version should be incremented. *)
let interface_format_version = "20"

(** Node argument *)
type arg = { a_name : name option; a_type : ty; a_linearity : linearity }

(** Node static parameters *)
type param = { p_name : name; p_type : ty }

(** Constraints on size expressions *)
type size_constraint =
  | Cequal of static_exp * static_exp (* e1 = e2 *)
  | Clequal of static_exp * static_exp (* e1 <= e2 *)
  | Cfalse

(** Node signature *)
type node = {
  node_inputs : arg list;
  node_outputs : arg list;
  node_stateful : bool;
  node_params : param list;
  node_params_constraints : size_constraint list }

type field = { f_name : field_name; f_type : ty }
type structure = field list

type type_def =
  | Tabstract
  | Talias of ty
  | Tenum of constructor_name list
  | Tstruct of structure

type const_def = { c_type : ty; c_value : static_exp }

let names_of_arg_list l = List.map (fun ad -> ad.a_name) l

let types_of_arg_list l = List.map (fun ad -> ad.a_type) l

let mk_arg ?(linearity = Ltop) name ty = { a_type = ty; a_linearity = linearity; a_name = name }

let mk_param name ty = { p_name = name; p_type = ty }

let mk_field n ty = { f_name = n; f_type = ty }

let mk_const_def ty value =
  { c_type = ty; c_value = value }

let mk_node ?(constraints = []) ins outs stateful params =
  { node_inputs = ins;
    node_outputs  = outs;
    node_stateful = stateful;
    node_params = params;
    node_params_constraints = constraints }

let rec field_assoc f = function
  | [] -> raise Not_found
  | { f_name = n; f_type = ty }::l ->
      if f = n then ty
      else field_assoc f l



