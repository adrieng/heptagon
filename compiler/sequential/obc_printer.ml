open Obc
open Format
open Pp_tools

let rec print_type ff = function
  | Tint    -> fprintf ff "int"
  | Tfloat  -> fprintf ff "float"
  | Tbool   -> fprintf ff "bool"
  | Tid(id) -> print_longname ff id
  | Tarray(ty, n) ->
      print_type ff ty;
      fprintf ff "^%d" n

let print_vd ff vd =
  fprintf ff "@[<v>";
  print_ident ff vd.v_ident;
  fprintf ff ": ";
  print_type ff vd.v_type;
  fprintf ff "@]"

let print_obj ff { cls = cls; obj = obj; size = n } =
  fprintf ff "@[<v>"; print_name ff obj;
  fprintf ff " : "; print_longname ff cls;
  if n <> 1 then
    fprintf ff "[%d]" n;
  fprintf ff ";@]"

let rec print_c ff = function
  | Cint i       -> fprintf ff "%d" i
  | Cfloat f     -> fprintf ff "%f" f
  | Cconstr(tag) -> print_longname ff tag
  | Carray(n,c) ->
      print_c ff c;
      fprintf ff "^%d" n

let rec print_lhs ff e =
  match e with
    | Var x           -> print_ident ff x
    | Mem x           -> fprintf ff "mem("; print_ident ff x; fprintf ff ")"
    | Field (l, f)    -> print_lhs ff l; fprintf ff ".%s" (shortname f)
    | Array(x, idx) ->
        print_lhs ff x;
        fprintf ff "[";
        print_exp ff idx;
        fprintf ff "]"

and print_exps ff e_list = print_list_r print_exp "" "," "" ff e_list

and print_exp ff = function
  | Lhs lhs -> print_lhs ff lhs
  | Const c         -> print_c ff c
  | Op(op, e_list) -> print_op ff op e_list
  | Struct_lit(_,f_e_list) ->
      fprintf ff "@[<v 1>";
      print_list_r
        (fun ff (field, e) -> print_longname ff field;fprintf ff " = ";
           print_exp ff e)
        "{" ";" "}" ff f_e_list;
      fprintf ff "@]"
  | Array_lit e_list ->
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
  | Context o -> print_name ff o
  | Array_context (o, i) ->
      fprintf ff "%a[%a]"
        print_name o
        print_lhs i

let rec print_act ff a =
  match a with
    | Assgn (x, e) -> print_asgn ff "" x e
    | Comp (a1, a2) ->
        fprintf ff "@[<v>";
        print_act ff a1;
        fprintf ff ";@,";
        print_act ff a2;
        fprintf ff "@]"
    | Case(e, tag_act_list) ->
        fprintf ff "@[<v>@[<v 2>switch (";
        print_exp ff e; fprintf ff ") {@,";
        print_tag_act_list ff tag_act_list;
        fprintf ff "@]@,}@]"
    | For(x, i1, i2, act) ->
        fprintf ff "@[<v>@[<v 2>for %s=%d to %d : {@, %a @]@,}@]"
          (name x) i1 i2
          print_act act
    | Step_ap (var_list, o, es) ->
        print_list print_lhs "(" "," ")" ff var_list;
        fprintf ff " = "; print_obj_call ff o; fprintf ff ".step(";
        fprintf ff "@["; print_exps ff es; fprintf ff "@]";
        fprintf ff ")"
    | Reinit o ->
        print_name ff o; fprintf ff ".reset()"
    | Nothing -> fprintf ff "()"

and print_tag_act_list ff tag_act_list =
  print_list
    (fun ff (tag, a) ->
       fprintf ff "@[<hov 2>case@ ";
       print_longname ff tag;
       fprintf ff ":@ ";
       print_act ff a;
       fprintf ff "@]") "" "" "" ff tag_act_list

let print_step ff { inp = inp; out = out; local = nl; bd = bd } =
  fprintf ff "@[<v 2>";
  fprintf ff "step(@[";
  print_list_r print_vd "(" ";" ")" ff inp;
  fprintf ff "@]) returns ";
  print_list_r print_vd "(" ";" ")" ff out;
  fprintf ff "@]){@,";
  if nl <> [] then begin
    fprintf ff "@[<hov 4>var ";
    print_list_r print_vd "" ";" "" ff nl;
    fprintf ff ";@]@,"
  end;
  print_act ff bd;
  fprintf ff "}@]"

let print_reset ff act =
  fprintf ff "@[<v 2>";
  fprintf ff "reset() {@,";
  print_act ff act;
  fprintf ff "}@]"

let print_def ff
    { cl_id = id; mem = mem; objs = objs; reset = reset; step = step } =
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
  print_reset ff reset;
  fprintf ff "@,";
  print_step ff step;
  fprintf ff "@]"

let print_type_def ff { t_name = name; t_desc = tdesc } =
  match tdesc with
    | Type_abs -> fprintf ff "@[type %s@\n@]" name
    | Type_enum(tag_name_list) ->
        fprintf ff "@[type %s = " name;
        print_list_r print_name "" "|" "" ff tag_name_list;
        fprintf ff "@\n@]"
    | Type_struct(f_ty_list) ->
        fprintf ff "@[type %s = " name;
        fprintf ff "@[<v 1>";
        print_list
          (fun ff (field, ty) ->
             print_name ff field;
             fprintf ff ": ";
             print_type ff ty) "{" ";" "}" ff f_ty_list;
        fprintf ff "@]@.@]"

let print_open_module ff name =
  fprintf ff "@[open ";
  print_name ff name;
  fprintf ff "@.@]"

let print_prog ff { o_opened = modules; o_types = types; o_defs = defs } =
  List.iter (print_open_module ff) modules;
  List.iter (print_type_def ff) types;
  List.iter (fun def -> (print_def ff def; fprintf ff "@ ")) defs

let print oc p =
  let ff = formatter_of_out_channel oc in
    fprintf ff "@[-- Code generated by the MiniLucid Compiler@.";
    fprintf ff "@[<v>"; print_prog ff p; fprintf ff "@]@]@."

