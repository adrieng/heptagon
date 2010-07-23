(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* Read an interface *)

open Idents
open Names
open Heptagon
open Signature
open Modules
open Typing
open Pp_tools
open Types

module Type =
struct
  let sigtype { sig_name = name; sig_inputs = i_list; sig_statefull = statefull;
                sig_outputs = o_list; sig_params = params } =
    let typed_params, const_env = build_node_params NamesEnv.empty params in
    let check_arg a = { a with a_type = check_type const_env a.a_type } in
    name, { node_inputs = List.map check_arg i_list;
            node_outputs = List.map check_arg o_list;
            node_statefull = statefull;
            node_params = typed_params;
            node_params_constraints = []; }

  let read { interf_desc = desc; interf_loc = loc } =
    try
      match desc with
        | Iopen(n) -> open_module n
        | Itypedef(tydesc) -> deftype tydesc
        | Iconstdef cd -> ignore (typing_const_dec cd)
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
  open Hept_printer

  let deftype ff name tdesc =
    match tdesc with
      | Tabstract -> fprintf ff "@[type %s@.@]" name
      | Tenum(tag_name_list) ->
          fprintf ff "@[<hov 2>type %s = " name;
          print_list_r print_name "" " |" "" ff tag_name_list;
          fprintf ff "@.@]"
      | Tstruct(f_ty_list) ->
          fprintf ff "@[<hov 2>type %s = " name;
          fprintf ff "@[<hov 1>";
          print_list_r
            (fun ff { f_name = field; f_type = ty } -> print_name ff field;
               fprintf ff ": ";
               print_type ff ty) "{" ";" "}" ff f_ty_list;
          fprintf ff "@]@.@]"

  let constdef ff _ c =
    fprintf ff "@[const ";
    print_name ff c.c_name;
    fprintf ff " : ";
    print_type ff c.c_type;
    fprintf ff " = ";
    print_static_exp ff c.c_value;
    fprintf ff "@.@]"

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
      | l -> print_list_r print_name "<<" "," ">>" ff l
    in

    fprintf ff "@[<v 2>val ";
    print_name ff name;
    print_node_params ff (List.map (fun p -> p.p_name) params);
    fprintf ff "@[";
    print_list_r print "(" ";" ")" ff inputs;
    fprintf ff "@] returns @[";
    print_list_r print "(" ";" ")" ff outputs;
    fprintf ff "@]";
    (match constr with
       | [] -> ()
       | constr ->
           fprintf ff "\n with: @[";
           print_list_r Static.print_size_constraint "" "," "" ff constr;
           fprintf ff "@]"
    );
    fprintf ff "@.@]"

  let print oc =
    let ff = formatter_of_out_channel oc in
    NamesEnv.iter (fun key typdesc -> deftype ff key typdesc) current.types;
    NamesEnv.iter (fun key constdec -> constdef ff key constdec) current.consts;
    NamesEnv.iter (fun key sigtype -> signature ff key sigtype) current.values;
end
