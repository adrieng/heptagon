open Obc
open Format
open Pp_tools
open Types
open Idents
open Names

let print_vd ff vd =
  fprintf ff "@[<v>";
  print_ident ff vd.v_ident;
  fprintf ff ": ";
  print_type ff vd.v_type;
  fprintf ff "@]"

let print_obj ff o =
  fprintf ff "@[<v>"; print_name ff o.o_name;
  fprintf ff " : "; print_longname ff o.o_class;
  fprintf ff "@[<2>%a@]" (print_list_r print_static_exp "<<"","">>") o.o_params;
  (match o.o_size with
     | Some se -> fprintf ff "[%a]" print_static_exp se
     | None -> ());
  fprintf ff ";@]"

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
          (fun ff (field, e) -> print_longname ff field;fprintf ff " = ";
             print_exp ff e)
          "{" ";" "}" ff f_e_list;
        fprintf ff "@]"
    | Earray e_list ->
        fprintf ff "@[";
        print_list_r print_exp "[" ";" "]" ff e_list;
        fprintf ff "@]"

and print_op ff op e_list =
  print_longname ff op;
  print_list_r print_exp "(" "," ")" ff e_list

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
        fprintf ff "@[<v>@[<v 2>switch (";
        print_exp ff e; fprintf ff ") {@,";
        print_tag_act_list ff tag_act_list;
        fprintf ff "@]@,}@]"
    | Afor(x, i1, i2, act_list) ->
        fprintf ff "@[<v>@[<v 2>for %s=%a to %a : {@, %a @]@,}@]"
          (name x)
          print_static_exp i1
          print_static_exp i2
          print_act_list act_list
    | Acall (var_list, o, meth, es) ->
        print_list print_lhs "(" "," ")" ff var_list;
        fprintf ff " = "; print_obj_call ff o;
        fprintf ff ".%a("  print_method_name meth;
        fprintf ff "@["; print_exps ff es; fprintf ff "@]";
        fprintf ff ")"

and print_act_list ff b =
  if b.b_locals <> [] then begin
    fprintf ff "@[<hov 4>var ";
    print_list_r print_vd "" ";" "" ff b.b_locals;
    fprintf ff ";@]@,"
  end;
  print_list_r print_act "" ";" "" ff b.b_body

and print_tag_act_list ff tag_act_list =
  print_list
    (fun ff (tag, a) ->
       fprintf ff "@[<hov 2>case@ ";
       print_longname ff tag;
       fprintf ff ":@ ";
       print_act_list ff a;
       fprintf ff "@]") "" "" "" ff tag_act_list

let print_method_name ff = function
  | Mreset -> fprintf ff "reset"
  | Mstep -> fprintf ff "step"
  | Mmethod n -> fprintf ff "%s" n

let print_method ff md =
  fprintf ff "@[<v 2>";
  print_method_name ff md.m_name;
  fprintf ff "(@[";
  print_list_r print_vd "(" ";" ")" ff md.m_inputs;
  fprintf ff "@]) returns ";
  print_list_r print_vd "(" ";" ")" ff md.m_outputs;
  fprintf ff "@]){@,";
  print_act_list ff md.m_body;
  fprintf ff "}@]"

let print_def ff
    { cd_name = id; cd_mems = mem; cd_objs = objs; cd_methods = m_list } =
  fprintf ff "@[<v 2>machine "; print_name ff id; fprintf ff " =@,";
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
  print_list_r print_method "" "\n" "" ff m_list;
  fprintf ff "@]"

let print_type_def ff { t_name = name; t_desc = tdesc } =
  match tdesc with
    | Type_abs -> fprintf ff "@[type %s@\n@]" name
    | Type_alias ty ->
        fprintf ff  "@[type %s@ = %a\n@]" name  print_type ty
    | Type_enum(tag_name_list) ->
        fprintf ff "@[type %s = " name;
        print_list_r print_name "" "|" "" ff tag_name_list;
        fprintf ff "@\n@]"
    | Type_struct(f_ty_list) ->
        fprintf ff "@[type %s = " name;
        fprintf ff "@[<v 1>";
        print_list
          (fun ff { Signature.f_name = field; Signature.f_type = ty } ->
             print_name ff field;
             fprintf ff ": ";
             print_type ff ty) "{" ";" "}" ff f_ty_list;
        fprintf ff "@]@.@]"

let print_open_module ff name =
  fprintf ff "@[open ";
  print_name ff name;
  fprintf ff "@.@]"

let print_const_dec ff c =
  fprintf ff "const %a = %a" print_name c.c_name
    print_static_exp c.c_value

let print_prog ff { p_opened = modules; p_types = types;
                    p_consts = consts; p_defs = defs } =
  List.iter (print_open_module ff) modules;
  List.iter (print_type_def ff) types;
  List.iter (print_const_dec ff) consts;
  List.iter (fun def -> (print_def ff def; fprintf ff "@ ")) defs

let print oc p =
  let ff = formatter_of_out_channel oc in
    fprintf ff "@[-- Code generated by the MiniLucid Compiler@.";
    fprintf ff "@[<v>"; print_prog ff p; fprintf ff "@]@]@."

