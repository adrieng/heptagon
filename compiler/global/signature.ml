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
open Location
open Linearity

(** Warning: Whenever these types are modified,
    interface_format_version should be incremented. *)
let interface_format_version = "30"

type ck =
  | Cbase
  | Con of ck * constructor_name * name

(** Node argument : inputs and outputs *)
type arg = {
  a_name  : name option;
  a_type  : ty;
  a_clock : ck; (** [a_clock] set to [Cbase] means at the node activation clock *)
  a_linearity : linearity;
}

(** Node static parameters *)
type param = { p_name : name; p_type : ty }

(** Constraints on size expressions *)
type constrnt = static_exp

(** Node signature *)
type node = {
  node_inputs             : arg list;
  node_outputs            : arg list;
  node_stateful           : bool;
  node_unsafe             : bool;
  node_params             : param list;
  node_param_constraints  : constrnt list;
  node_loc                : location}

type field = { f_name : field_name; f_type : ty }
type structure = field list

type type_def =
  | Tabstract
  | Talias of ty
  | Tenum of constructor_name list
  | Tstruct of structure

type const_def = { c_type : ty; c_value : static_exp }


(** { 3 Signature helper functions } *)

type error =
  | Eckvar_unbound_input of name option * name
  | Eckvar_unbound_ouput of name option * name

exception SignatureError of name option * name

let message loc e = begin match e with
  | Eckvar_unbound_input(var_name,ck_name) ->
      let a,name = match var_name with None -> "A","" | Some n -> "The"," "^n in
      Format.eprintf "%a%s sampled input%s should come together with its sampling variable %s.@."
        print_location loc
        a name ck_name
  | Eckvar_unbound_ouput (var_name,ck_name) ->
      let a,name = match var_name with None -> "A","" | Some n -> "The"," "^n in
      Format.eprintf "%a%s sampled ouput%s should be returned with its sampling value %s.@."
        print_location loc
        a name ck_name
  end;
  raise Errors.Error


(** @raise Errors.Error after printing the error *)
let check_signature s =
  (* a simple env of defined names will be used, represented by a Set *)
  let rec append env sa_l = match sa_l with
    | [] -> env
    | sa::sa_l -> match sa.a_name with
        | None -> append env sa_l
        | Some x -> append (NamesSet.add x env) sa_l
  in
  (* the clock of [arg] is correct if all the vars used are in [env] *)
  let check env arg =
    let n = arg.a_name in
    let rec f = function
      | Cbase -> ()
      | Con(ck,_,x) ->
          if not (NamesSet.mem x env)
          then raise (SignatureError (n,x));
          f ck
    in
    f arg.a_clock
  in
  (*initial env with only the inputs*)
  let env = append NamesSet.empty s.node_inputs in
  (try List.iter (check env) s.node_inputs
  with SignatureError (x,c) ->
    message s.node_loc (Eckvar_unbound_input (x,c)));
  let env = append env s.node_outputs in
  try List.iter (check env) s.node_outputs
  with SignatureError (x,c) ->
    message s.node_loc (Eckvar_unbound_ouput (x,c))


let rec ck_to_sck ck =
  let ck = Clocks.ck_repr ck in
  match ck with
    | Clocks.Cbase -> Cbase
    | Clocks.Con (ck,c,x) -> Con(ck_to_sck ck, c, Idents.source_name x)
    | _ -> Misc.internal_error "Signature couldn't translate ck"


let names_of_arg_list l = List.map (fun ad -> ad.a_name) l

let types_of_arg_list l = List.map (fun ad -> ad.a_type) l

let types_of_param_list l = List.map (fun p -> p.p_type) l

let linearities_of_arg_list l = List.map (fun ad -> ad.a_linearity) l

let mk_arg name ty linearity ck =
  { a_type = ty; a_linearity = linearity; a_name = name; a_clock = ck }

let mk_param name ty = { p_name = name; p_type = ty }

let mk_field n ty = { f_name = n; f_type = ty }

let mk_const_def ty value =
  { c_type = ty; c_value = value }

let mk_node ?(constraints = []) loc ins outs stateful unsafe params =
  { node_inputs = ins;
    node_outputs  = outs;
    node_stateful = stateful;
    node_unsafe = unsafe;
    node_params = params;
    node_param_constraints = constraints;
    node_loc = loc}

let rec field_assoc f = function
  | [] -> raise Not_found
  | { f_name = n; f_type = ty }::l ->
      if f = n then ty
      else field_assoc f l



