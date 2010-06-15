(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* Read an interface *)

(* $Id$ *)

open Misc
open Ident
open Names
open Linearity
open Heptagon
open Global
open Modules
open Typing

let rec split3 = function
  | [] -> [], [], []
  | (a,b,c)::l ->
      let a_list, b_list, c_list = split3 l in
	a::a_list, b::b_list, c::c_list

let rec combine3 l1 l2 l3 = match l1, l2, l3 with
  | [], [], [] -> []
  | a::a_list, b::b_list, c::c_list ->
      (a,b,c)::(combine3 a_list b_list c_list)

module Type =
  struct
    let sigtype { sig_name = name; sig_inputs = i_list; sig_outputs = o_list; 
		  sig_node = node; sig_safe = safe; sig_params = params } =
      let arg_dec_of_tuple (n, ty, l) = 
	{ a_name = n;
	  a_type = Tbase(check_type ty);
	  a_linearity = l;
	  a_pass_by_ref = false } in
      let i_inputs, t_inputs, l_inputs = split3 i_list in
      let o_outputs, t_outputs, l_outputs = split3 o_list in
	name, { inputs = List.map arg_dec_of_tuple i_list;
		outputs = List.map arg_dec_of_tuple o_list;
		contract = None;
		node = node;
		safe = safe; 
	        targeting = [];
		params = params;
		params_constraints = []; }
	  
    let read { interf_desc = desc; interf_loc = loc } =
      try
	match desc with
	  | Iopen(n) -> open_module n
	  | Itypedef(tydesc) -> deftype NamesEnv.empty tydesc
	  | Isignature(s) -> 
	      let name, s = sigtype s in
		add_value name s
      with
	  TypingError(error) -> message loc error

    let main l = 
      List.iter read l
  end
    
module Printer =
struct
  open Format
  open Printer
    
  let deftype ff name tdesc =
    match tdesc with
      | Tabstract -> fprintf ff "@[type %s@.@]" name
      | Tenum(tag_name_list) ->
	  fprintf ff "@[<hov 2>type %s = " name;
	  print_list ff print_name " |" tag_name_list;
	  fprintf ff "@.@]"
      | Tstruct(f_ty_list) ->
	  fprintf ff "@[<hov 2>type %s = " name;
	  fprintf ff "@[<hov 1>{";
	  print_list ff 
	    (fun ff (field, ty) -> print_name ff field;
              fprintf ff ": ";
	      print_base_type ff ty) ";" f_ty_list;
	  fprintf ff "}@]@.@]"

  let signature ff name { inputs = inputs;
			  outputs = outputs;
			  contract = contract; node = node;
			  safe = safe; params = params; params_constraints = constr } =
    let print ff arg =
      match arg.a_name with
	| None -> print_type ff arg.a_type
	| Some(name) -> 
	    print_name ff name; fprintf ff ":"; print_type ff arg.a_type;
	    fprintf ff " "; print_lin ff arg.a_linearity in

    let print_node_params ff = function
      | [] -> ()
      | l -> 
	  fprintf ff "<<";
	  print_list ff print_name "," l;
	  fprintf ff ">>" in
      
    fprintf ff "@[<v 2>val ";
    if safe then fprintf ff "safe ";
    if node then fprintf ff "node " else fprintf ff "fun ";
    print_name ff name;
    print_node_params ff params;
    fprintf ff "(@[";
    print_list ff print ";" inputs;
    fprintf ff "@]) returns (@[";
    print_list ff print ";" outputs;
    fprintf ff "@])";
    (match constr with
       | [] -> ()
       | constr -> 
	   fprintf ff "\n with: @[";
	   print_list ff Static.print_size_constr "," constr;
	   fprintf ff "@]"
    );
    optunit (print_contract ff) contract;
    fprintf ff "@.@]"
	
  let print oc =
    let ff = formatter_of_out_channel oc in
    NamesEnv.iter (fun key typdesc -> deftype ff key typdesc) current.types;
    NamesEnv.iter (fun key sigtype -> signature ff key sigtype) current.values;
end
