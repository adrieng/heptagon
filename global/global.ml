(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* global data in the symbol tables *)
(* $Id$ *)
open Names
open Ident
open Linearity
open Heptagon
open Static

(** Warning: Whenever these types are modified, 
    interface_format_version in misc.ml should be incremented. *)
type arg_dec = 
    { a_type : ty;
      a_name : name option;
      a_linearity : linearity;
      a_pass_by_ref: bool; }

type sig_desc = 
    { inputs : arg_dec list;
      outputs : arg_dec list;
      contract : contract option;
      node : bool;
      safe : bool; 
      targeting : (int*int) list; 
      params: name list;
      params_constraints : size_constr list; }

and field_desc =
    { arg: base_ty; (* if x:arg then x.m: res *)
      res: base_ty;
    }

and struct_desc = 
    { fields : (name * base_ty) list; }

and typ_desc =
    | Tabstract
    | Tenum of name list
    | Tstruct of (name * base_ty) list

type 'a info = { qualid : qualident; info : 'a }

type ivar =
  | IVar of ident
  | IField of ident * longname

(** [filter_vars l] returns a list of variables identifiers from
    a list of ivar.*)
let rec filter_vars = function
  | [] -> []
  | (IVar id)::l -> id::(filter_vars l)
  | _::l -> filter_vars l

let names l =
  List.map (fun ad -> ad.a_name) l

let types l =
  List.map (fun ad -> ad.a_type) l

let linearities l =
  List.map (fun ad -> ad.a_linearity) l
