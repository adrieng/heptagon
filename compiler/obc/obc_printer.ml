(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)
open Obc
open Format
open Pp_tools
open Names
open Global_printer

let print_vd ff vd =
  fprintf ff "@[<v>";
  if vd.v_mutable then
    fprintf ff "mutable ";
  print_ident ff vd.v_ident;
  fprintf ff ": ";
  print_type ff vd.v_type;
  fprintf ff "@]"

let print_obj ff o =
  fprintf ff "@[<v>"; print_ident ff o.o_ident;
  fprintf ff " : "; print_qualname ff o.o_class;
  fprintf ff "@[<2>%a@]" (print_list_r print_static_exp "<<"","">>") o.o_params;
  (match o.o_size with
     | Some se -> fprintf ff "%a" (print_list_r print_static_exp "[" "][" "]") se
     | None -> ());
  fprintf ff "@]"

let rec print_lhs ff e =
  match e.pat_desc with
    | Lvar x -> print_ident ff x
    | Lmem x -> fprintf ff "mem("; print_ident ff x; fprintf ff ")"
    | Lfield (l, f) -> print_lhs ff l; fprintf ff ".%s" (shortname f)
    | Larray(x, idx) ->
        print_lhs ff x;
        fprintf ff "[";
        print_exp ff idx;
        fprintf ff "]"

and print_ext_value ff w = match w.w_desc with
  | Wvar x -> print_ident ff x
  | Wconst c -> print_static_exp ff c
  | Wmem x -> fprintf ff "mem("; print_ident ff x; fprintf ff ")"
  | Wfield (l, f) -> print_ext_value ff l; fprintf ff ".%s" (shortname f)
  | Warray(x, idx) ->
    print_ext_value ff x;
    fprintf ff "[";
    print_exp ff idx;
    fprintf ff "]"


and print_exps ff e_list = print_list_r print_exp "" "," "" ff e_list

and print_exp ff e =
  match e.e_desc with
    | Eextvalue lhs -> print_ext_value ff lhs
    | Eop(op, e_list) -> print_op ff op e_list
    | Estruct(_,f_e_list) ->
        fprintf ff "@[<v 1>";
        print_list_r
          (fun ff (field, e) -> print_qualname ff field;fprintf ff " = ";
             print_exp ff e)
          "{" ";" "}" ff f_e_list;
        fprintf ff "@]"
    | Earray e_list ->
        fprintf ff "@[";
        print_list_r print_exp "[" ";" "]" ff e_list;
        fprintf ff "@]"

and print_op ff op e_list = match e_list with
  | [l; r] ->
      fprintf ff "(@[%a@ %a %a@])" print_qualname op print_exp l print_exp r
  | _ ->
      print_qualname ff op;
      print_list_l print_exp "(" "," ")" ff e_list

let print_asgn ff pref x e =
  fprintf ff "@[%s" pref; print_lhs ff x; fprintf ff " = ";
  fprintf ff "@["; print_exp ff e; fprintf ff "@]";
  fprintf ff "@]"

let print_obj_call ff = function
  | Oobj o -> print_ident ff o
  | Oarray (o, i) ->
      fprintf ff "%a%a"
        print_ident o
        (print_list_r print_lhs "[" "][" "]") i

let print_method_name ff = function
  | Mstep -> fprintf ff "step"
  | Mreset -> fprintf ff "reset"


let rec print_act ff a =
  let print_lhs_tuple ff var_list = match var_list with
    | [] -> ()
    | _ -> fprintf ff "@[(%a)@] =@ " (print_list print_lhs "" "," "") var_list in
  match a with
    | Aassgn (x, e) -> print_asgn ff "" x e
    | Acase(e, tag_act_list) ->
        fprintf ff "@[<v>@[<v 2>switch (";
        print_exp ff e; fprintf ff ") {@ ";
        print_tag_act_list ff tag_act_list;
        fprintf ff "@]@,}@]"
    | Afor(x, i1, i2, act_list) ->
        fprintf ff "@[<v>@[<v 2>for %a = %a to %a {@  %a @]@,}@]"
          print_vd x
          print_exp i1
          print_exp i2
          print_block act_list
    | Aop (op, es) ->
        print_op ff op es
    | Acall (var_list, o, meth, es) ->
        fprintf ff "@[<2>%a%a.%a(%a)@]"
          print_lhs_tuple var_list
          print_obj_call o
          print_method_name meth
          print_exps es
    | Ablock b ->
        fprintf ff "do@\n  %a@\ndone" print_block b

and print_var_dec_list ff var_dec_list = match var_dec_list with
  | [] -> ()
  | _ ->
      fprintf ff "@[<hov 4>%a@]@ "
        (print_list_r print_vd "var " ";" ";") var_dec_list

and print_block ff b =
  fprintf ff "@[<v>%a%a@]"
    print_var_dec_list b.b_locals
    (print_list_r print_act "" ";" "") b.b_body

and print_tag_act_list ff tag_act_list =
  print_list
    (fun ff (tag, a) ->
       fprintf ff "@[<v 2>case %a:@ %a@]"
         print_qualname tag
         print_block a)
    "" "" "" ff tag_act_list

let print_method_name ff = function
  | Mreset -> fprintf ff "reset"
  | Mstep -> fprintf ff "step"

let print_arg_list ff var_list =
  fprintf ff "(@[%a@])" (print_list_r print_vd "" "," "") var_list

let print_method ff md =
  fprintf ff "@[<v 2>@[%a%a@ returns %a {@]@ %a@]@\n}"
    print_method_name md.m_name
    print_arg_list md.m_inputs
    print_arg_list md.m_outputs
    print_block md.m_body

let print_class_def ff
		    { cd_name = id;
		      cd_mems = mem;
		      cd_objs = objs;
		      cd_params = params;
		      cd_methods = m_list;
		    } =
  fprintf ff "@[<v 2>machine "; print_qualname ff id;
  if params <> [] then
    begin
      fprintf ff "@[<hov 2>";
      print_list_r print_param "<<" "," ">>" ff params;
      fprintf ff "@]";
    end;
  fprintf ff " =@,";
  if mem <> [] then begin
    fprintf ff "@[<hov 4>var ";
    print_list_r print_vd "" ";" "" ff mem;
    fprintf ff ";@]@,"
  end;
  if objs <> [] then begin
    fprintf ff "@[<hov 4>obj ";
    print_list print_obj "" ";" "" ff objs;
    fprintf ff ";@]@,"
  end;
  if mem <> [] || objs <> [] then fprintf ff "@,";
  print_list_r print_method "" "\n" "" ff m_list;
  fprintf ff "@]"


let print_type_def ff { t_name = name; t_desc = tdesc } =
  match tdesc with
    | Type_abs -> fprintf ff "@[type %a@\n@]" print_qualname name
    | Type_alias ty ->
        fprintf ff  "@[type %a@ = %a@\n@]" print_qualname name  print_type ty
    | Type_enum(tag_name_list) ->
        fprintf ff "@[type %a = " print_qualname name;
        print_list_r print_qualname "" "|" "" ff tag_name_list;
        fprintf ff "@\n@]"
    | Type_struct(f_ty_list) ->
        fprintf ff "@[type %a = " print_qualname name;
        fprintf ff "@[<v 1>";
        print_list
          (fun ff { Signature.f_name = field; Signature.f_type = ty } ->
             print_qualname ff field;
             fprintf ff ": ";
             print_type ff ty) "{" ";" "}" ff f_ty_list;
        fprintf ff "@]@.@]"

let print_open_module ff name =
  fprintf ff "open %s@." (modul_to_string name)

let print_const_dec ff c =
  fprintf ff "const %a = %a@." print_qualname c.c_name
    print_static_exp c.c_value

let print_prog_desc ff pd = match pd with
  | Pclass cd -> print_class_def ff cd; fprintf ff "@\n@\n"
  | Pconst cd -> print_const_dec ff cd
  | Ptype td -> print_type_def ff td

let print_prog ff { p_opened = modules; p_desc = descs } =
  List.iter (print_open_module ff) modules;
  List.iter (print_prog_desc ff) descs

let print oc p =
  let ff = formatter_of_out_channel oc in
  fprintf ff "@[-- Code generated by the MiniLucid Compiler@.";
  fprintf ff "@[<v>"; print_prog ff p; fprintf ff "@]@]@."
