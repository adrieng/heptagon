(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* Read an interface *)

open Ident
open Names
open Heptagon
open Signature
open Modules
open Typing

module Type =
  struct
    let sigtype { sig_name = name; sig_inputs = i_list; 
                  sig_outputs = o_list; sig_params = params } =
	      name, { node_inputs = i_list;
		            node_outputs = o_list;
		            node_params = params;
		            node_params_constraints = []; }
	  
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
	             print_type ff ty) ";" f_ty_list;
	        fprintf ff "}@]@.@]"

  let signature ff name { node_inputs = inputs;
			  node_outputs = outputs;
			  node_params = params; 
        node_params_constraints = constr } =
    let print ff arg =
      match arg.a_name with
	      | None -> print_type ff arg.a_type
	      | Some(name) -> 
	          print_name ff name; fprintf ff ":"; print_type ff arg.a_type
    in

    let print_node_params ff = function
      | [] -> ()
      | l -> 
	        fprintf ff "<<";
	        print_list ff print_name "," l;
	        fprintf ff ">>" in
      
      fprintf ff "@[<v 2>val ";
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
      fprintf ff "@.@]"
	      
  let print oc =
    let ff = formatter_of_out_channel oc in
    NamesEnv.iter (fun key typdesc -> deftype ff key typdesc) current.types;
    NamesEnv.iter (fun key sigtype -> signature ff key sigtype) current.values;
end
