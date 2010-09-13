open Obc
open Format
open Pp_tools
open Types
open Idents
open Names
open Global_printer

let print_vd ff vd =
  fprintf ff "@[<v>";
  print_ident ff vd.v_ident;
  fprintf ff ": ";
  print_type ff vd.v_type;
  fprintf ff "@]"

let print_obj ff o =
  fprintf ff "@[<v>"; print_name ff o.o_name;
  fprintf ff " : "; print_qualname ff o.o_class;
  fprintf ff "@[<2>%a@]" (print_list_r print_static_exp "<<"","">>") o.o_params;
  (match o.o_size with
     | Some se -> fprintf ff "[%a]" print_static_exp se
     | None -> ());
  fprintf ff "@]"

let rec print_lhs ff e =
  match e.l_desc with
    | Lvar x -> print_ident ff x
    | Lmem x -> fprintf ff "mem("; print_ident ff x; fprintf ff ")"
    | Lfield (l, f) -> print_lhs ff l; fprintf ff ".%s" (shortname f)
    | Larray(x, idx) ->
        print_lhs ff x;
        fprintf ff "[";
        print_exp ff idx;
        fprintf ff "]"

and print_exps ff e_list = print_list_r print_exp "" "," "" ff e_list

and print_exp ff e =
  match e.e_desc with
    | Elhs lhs -> print_lhs ff lhs
    | Econst c -> print_static_exp ff c
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
  | Oobj o -> print_name ff o
  | Oarray (o, i) ->
      fprintf ff "%a[%a]"
        print_name o
        print_lhs i

let print_method_name ff = function
  | Mstep -> fprintf ff "step"
  | Mreset -> fprintf ff "reset"
  | Mmethod n -> fprintf ff "%s" n

let rec print_act ff a =
  match a with
    | Aassgn (x, e) -> print_asgn ff "" x e
    | Acase(e, tag_act_list) ->
        fprintf ff "@[<v>@[<hv 2>switch (";
        print_exp ff e; fprintf ff ") {@ ";
        print_tag_act_list ff tag_act_list;
        fprintf ff "@]@,}@]"
    | Afor(x, i1, i2, act_list) ->
        fprintf ff "@[<v>@[<v 2>for %s = %a to %a {@, %a @]@,}@]"
          (name x)
          print_static_exp i1
          print_static_exp i2
          print_block act_list
    | Acall (var_list, o, meth, es) ->
        let print_lhs_tuple ff var_list = match var_list with
          | [] -> ()
          | _ ->
              fprintf ff "@[(%a)@] =@ "
                (print_list print_lhs "" "," "") var_list in

        fprintf ff "@[<2>%a%a.%a(%a)@]"
          print_lhs_tuple var_list
          print_obj_call o
          print_method_name meth
          print_exps es

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
  | Mmethod n -> fprintf ff "%s" n

let print_arg_list ff var_list =
  fprintf ff "(@[%a@])" (print_list_r print_vd "" "," "") var_list

let print_method ff md =
  fprintf ff "@[<v 2>@[%a%a@ returns %a {@]@ %a@]@\n}"
    print_method_name md.m_name
    print_arg_list md.m_inputs
    print_arg_list md.m_outputs
    print_block md.m_body

let print_class_def ff
    { cd_name = id; cd_mems = mem; cd_objs = objs; cd_methods = m_list } =
  fprintf ff "@[<v 2>machine "; print_qualname ff id; fprintf ff " =@,";
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
        print_list_r print_name "" "|" "" ff tag_name_list;
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
  fprintf ff "@[open ";
  print_name ff name;
  fprintf ff "@.@]"

let print_const_dec ff c =
  fprintf ff "const %a = %a@." print_qualname c.c_name
    print_static_exp c.c_value

let print_prog ff { p_opened = modules; p_types = types;
                    p_consts = consts; p_defs = defs } =
  List.iter (print_open_module ff) modules;
  List.iter (print_type_def ff) types;
  List.iter (print_const_dec ff) consts;
  fprintf ff "@\n";
  List.iter (fun def -> (print_class_def ff def; fprintf ff "@\n@\n")) defs

let print oc p =
  let ff = formatter_of_out_channel oc in
  fprintf ff "@[-- Code generated by the MiniLucid Compiler@.";
  fprintf ff "@[<v>"; print_prog ff p; fprintf ff "@]@]@."

