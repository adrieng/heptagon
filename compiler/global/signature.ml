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
let interface_format_version = "8"

(** Node argument *)
type arg = { a_name : name option; a_type : ty }

(** Node static parameters *)
type param = { p_name : name; p_type : ty }

(** Node signature *)
type node =
    { node_inputs : arg list;
      node_outputs : arg list;
      node_statefull : bool;
      node_params : param list; (** Static parameters *)
      node_params_constraints : size_constraint list }

type field = { f_name : name; f_type : ty }
type structure = field list

type type_def = | Tabstract | Tenum of name list | Tstruct of structure


let names_of_arg_list l = List.map (fun ad -> ad.a_name) l

let types_of_arg_list l = List.map (fun ad -> ad.a_type) l

let mk_arg name ty = { a_type = ty; a_name = name }

let mk_param name ty = { p_name = name; p_type = ty }

let mk_field n ty = { f_name = n; f_type = ty }


let print_param ff p =
  fprintf ff "%a:%a"  Names.print_name p.p_name  print_type p.p_type

let rec field_assoc f = function
  | [] -> raise Not_found
  | { f_name = n; f_type = ty }::l ->
      if shortname f = n then
        ty
      else
        field_assoc f l
