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
open Static

(** Warning: Whenever these types are modified,
    interface_format_version should be incremented. *)
let interface_format_version = "6"

(** Node argument *)
type arg = { a_type : ty; a_name : name option }

type param = { p_name : name }

(** Node signature *)
type node =
  { node_inputs : arg list;
    node_outputs : arg list;
    node_params : param list; (** Static parameters *)
    node_params_constraints : size_constr list }

type structure = (name * ty) list

type type_def = | Tabstract | Tenum of name list | Tstruct of structure


let names_of_arg_list l = List.map (fun ad -> ad.a_name) l

let types_of_arg_list l = List.map (fun ad -> ad.a_type) l

let mk_arg name ty =
  { a_type = ty; a_name = name }

let mk_param name = 
  { p_name = name }

