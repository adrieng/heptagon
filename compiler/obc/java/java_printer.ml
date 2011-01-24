(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* Java printer *)

open Java
open Pp_tools
open Format

(* TODO java faire des vrais qualname recursifs, bare_constructor doit être vraiment bare *)

let class_name = Global_printer.print_shortname
let obj_ident = Global_printer.print_ident
let constructor_name = Global_printer.print_qualname
let bare_constructor_name = Global_printer.print_shortname
let method_name = pp_print_string
let field_name = pp_print_string
let field_ident = Global_printer.print_ident
let op_name = Global_printer.print_qualname (* TODO java fix this for infix etc... see others is_infix and old_java *)
let var_ident = Global_printer.print_ident
let const_name = Global_printer.print_qualname

let rec ty ff t = match t with
  | Tbool -> fprintf ff "boolean"
  | Tint -> fprintf ff "int"
  | Tfloat -> fprintf ff "float"
  | Tclass n -> class_name ff n
  | Tgeneric (n, ty_l) -> fprintf ff "%a<@[%a@]>" class_name n (print_list_r ty """,""") ty_l
  | Tarray (t,_) -> fprintf ff "%a[]" ty t
  | Tunit -> pp_print_string ff "void"

let protection ff = function
  | Ppublic -> fprintf ff "public "
  | Pprotected -> fprintf ff "protected "
  | Pprivate -> fprintf ff "private "
  | Ppackage -> ()

let var_dec ff vd = fprintf ff "%a %a" ty vd.vd_type var_ident vd.vd_ident

let vd_list s1 s2 s3 ff vd_l = print_list_r var_dec s1 s2 s3 ff vd_l

let static ff s = if s then fprintf ff "static " else ()

let final ff f = if f then fprintf ff "final " else ()

let rec field ff f =
  fprintf ff "@[<2>%a%a%a%a %a%a;@]"
    protection f.f_protection
    static f.f_static
    final f.f_final
    ty f.f_type
    field_ident f.f_name
    (print_opt2 exp " = ") f.f_value

and exp ff = function
  | Eval p -> pattern ff p
  | Efun (f,e_l) -> fprintf ff "%a@[%a@]" op_name f args e_l
  | Emethod_call (o,m,e_l) -> fprintf ff "%a.%a%a" pattern o method_name m args e_l
  | Enew (c,e_l) -> fprintf ff "new %a%a" ty c args e_l
  | Enew_array (t,e_l) -> fprintf ff "new %a@[<2>%a@]" ty t (print_list_r exp "{"",""}") e_l
  | Evoid -> ()
  | Svar c -> const_name ff c
  | Sint i -> pp_print_int ff i
  | Sfloat f -> pp_print_float ff f
  | Sbool b -> pp_print_bool ff b
  | Sconstructor c -> constructor_name ff c

and args ff e_l = fprintf ff "@[(%a)@]" (print_list_r exp """,""") e_l

and pattern ff = function
  | Pfield (p,f) -> fprintf ff "%a.%a" pattern p field_name f
  | Pvar v -> var_ident ff v
  | Parray_elem (p,e) -> fprintf ff "%a[%a]" pattern p exp e
  | Pthis f -> fprintf ff "this.%a" field_ident f

let rec block ff b =
  fprintf ff "@[<v>%a@ %a@]"
    (vd_list """;"";") b.b_locals
    (print_list_r act """;"";") b.b_body

and act ff = function
  | Anewvar (vd,e) -> fprintf ff "%a = %a" var_dec vd exp e
  | Aassgn (p,e) -> fprintf ff "%a = %a" pattern p exp e
  | Amethod_call (o,m,e_l) -> fprintf ff "%a.%a%a" pattern o method_name m args e_l
  | Aswitch (e, c_b_l) ->
      let pcb ff (c,b) = fprintf ff "@[<hov 2>case %a:@ %a@ break;@]" bare_constructor_name c block b in
      fprintf ff "@[<v4>switch (%a) {@ %a@]@\n}"
        exp e
        (print_list_r pcb """""") c_b_l
  | Aif (e,bt) ->
      fprintf ff "@[<2>if (%a) {@ %a@ }@]" exp e block bt
  | Aifelse (e,bt,bf) ->
      fprintf ff "@[<2>if (%a) {@ %a@ }@]@\n@[<2>else {@ %a@ }@]"
        exp e
        block bt
        block bf
  | Ablock b -> fprintf ff "@[<2>{@ %a@ }]" block b
  | Afor (x, i1, i2, b) ->
        fprintf ff "@[<2>for (%a = %a; %a<%a; %a++) {@ %a@ }@]"
          var_dec x
          exp i1
          var_ident x.vd_ident
          exp i2
          var_ident x.vd_ident
          block b
  | Areturn e -> fprintf ff "return %a" exp e

let methode ff m =
  fprintf ff "@[<4>%a%a%a %a @[<2>(%a)@] {@\n%a@]@\n}"
    protection m.m_protection
    static m.m_static
    ty m.m_returns
    method_name m.m_name
    (vd_list """,""") m.m_args
    block m.m_body

let constructor ff m =
  fprintf ff "@[<4>%a%a @[<2>(%a)@] {@\n%a@]@\n}"
    protection m.m_protection
    method_name m.m_name
    (vd_list """,""") m.m_args
    block m.m_body

let rec class_desc ff cd =
  fprintf ff "@[<v>%a@ %a@ %a@ %a@]"
    (print_list_r field """;"";") cd.cd_fields
    (print_list_r classe """""") cd.cd_classs
    (print_list constructor """""") cd.cd_constructors
    (print_list methode """""") cd.cd_methodes

and classe ff c = match c.c_kind with
  | Cenum c_l ->
      fprintf ff "@[<4>%a%aenum %a {@\n%a@]@\n}"
        protection c.c_protection
        static c.c_static
        class_name c.c_name
        (print_list_r bare_constructor_name """,""") c_l
  | Cgeneric cd ->
      fprintf ff "@[<4>%a%aclass %a {@\n%a@]@\n}"
        protection c.c_protection
        static c.c_static
        class_name c.c_name
        class_desc cd

let output_classe dir c =
  let { Names.name = file_name; Names.qual = package_name } = c.c_name in
  let file_name = file_name ^ ".java" in
  let oc = open_out (Filename.concat dir file_name) in
  let ff = Format.formatter_of_out_channel oc in
  fprintf ff "package %s;@\n" (String.lowercase package_name);
  classe ff c;
  pp_print_flush ff ();
  close_out oc

let output_program dir (p:Java.program) =
  List.iter (output_classe dir) p

