(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* global data in the symbol tables *)

open Misc
open Names
open Location
open Linearity

(** Warning: Whenever these types are modified,
    interface_format_version should be incremented. *)
let interface_format_version = "4"

(***************************************************************************)
(* Types *)

type future_t = unit
and async_t = (static_exp list) option

and ck =
  | Cbase
  | Con of ck * constructor_name * name

and static_exp = { se_desc: static_exp_desc; se_ty: ty; se_loc: location }

and static_exp_desc =
  | Sfun of fun_name * (static_exp list) (** f<<3, n>> *)
  | Svar of constant_name
  | Sint of int
  | Sfloat of float
  | Sbool of bool
  | Sstring of string (** without enclosing quotes *)
  | Sconstructor of constructor_name
  | Sfield of field_name (** used as argument of Minils.Efield_update, doesn't exists in Obc. *)
  | Stuple of static_exp list
  | Sarray_power of static_exp * (static_exp list) (** power : 0^n^m : [[0,0,..],[0,0,..],..] *)
  | Sarray of static_exp list (** [ e1, e2, e3 ] *)
  | Srecord of (field_name * static_exp) list (** { f1 = e1; f2 = e2; ... } *)
  | Sop of fun_name * static_exp list (** defined ops for now in pervasives *)
  | Sasync of static_exp

and ty =
  | Tprod of ty list (** Product type used for tuples *)
  | Tid of type_name (** Usable type_name are alias or pervasives {bool,int,float} (see [Initial])*)
  | Tarray of ty * static_exp (** [base_type] * [size] *) (* ty should not be prod *)
  | Tinvalid
  | Tfuture of future_t * ty

and param = { p_name : name; p_type : param_ty }

and param_ty =
  | Ttype of ty
  | Tsig of node

(** Node argument : inputs and outputs *)
and arg = {
  a_name  : name option;
  a_type  : ty;
  a_clock : ck; (** [a_clock] set to [Cbase] means at the node activation clock *)
  a_linearity : linearity;
  (** [a_is_memory] is only correct after entering Minils (corrected with the Is_memory pass *)
  a_is_memory : bool;
}

(** Constraints on size expressions *)
and constrnt = static_exp

(** Node signature *)
and node = {
  node_inputs             : arg list;
  node_outputs            : arg list;
  node_stateful           : bool;
  node_unsafe             : bool;
  node_params             : param list;
  node_param_constraints  : constrnt list;
  node_external           : bool;
  node_loc                : location}

type field = { f_name : field_name; f_type : ty }
type structure = field list

type type_def =
  | Tabstract
  | Talias of ty
  | Tenum of constructor_name list
  | Tstruct of structure

type const_def = { c_type : ty; c_value : static_exp }


(** { 3 Helper functions } *)

let invalid_type = Tinvalid (** Invalid type given to untyped expression etc. *)

let prod = function
  | [ty]    -> ty
  | ty_list -> Tprod ty_list

let unprod = function
  | Tprod l -> l
  | t -> [t]


let asyncify async ty_list = match async with
  | None -> ty_list
  | Some _ -> List.map (fun ty -> Tfuture ((),ty)) ty_list

let mk_static_exp ?(loc = no_location) ty desc = (*note ~ty: replace as first arg*)
  { se_desc = desc; se_ty = ty; se_loc = loc }

let dummy_static_exp ty = mk_static_exp ty (Svar Names.dummy_qualname)

let names_of_arg_list l = List.map (fun ad -> ad.a_name) l

let types_of_arg_list l = List.map (fun ad -> ad.a_type) l

let types_of_param_list l = List.map (fun p -> p.p_type) l

let linearities_of_arg_list l = List.map (fun ad -> ad.a_linearity) l

let mk_arg ~is_memory ty linearity ck name =
  { a_type = ty; a_linearity = linearity; a_name = name; a_clock = ck;
    a_is_memory = is_memory }

let mk_param ty name = { p_name = name; p_type = ty }

let mk_field ty name = { f_name = name; f_type = ty }

let mk_const_def ty value =
  { c_type = ty; c_value = value }

let dummy_const ty = mk_const_def ty (dummy_static_exp ty)
let mk_node constraints loc ~extern ins outs stateful unsafe params =
  { node_inputs = ins;
    node_outputs  = outs;
    node_stateful = stateful;
    node_unsafe = unsafe;
    node_params = params;
    node_param_constraints = constraints;
    node_external = extern;
    node_loc = loc}

let dummy_node =
  mk_node [] ~extern:true no_location [] [] false false []

let rec field_assoc f = function
  | [] -> raise Not_found
  | { f_name = n; f_type = ty }::l ->
      if f = n then ty
      else field_assoc f l



