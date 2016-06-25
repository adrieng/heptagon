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

(* Java printer *)

open Java
open Pp_tools
open Format


let print_ident ff id =  Format.fprintf ff "%s" (jname_of_name (Idents.name id))

let print_qualname ff ({ Names.name = n } as qn) =
  Global_printer.print_qualname ff { qn with Names.name = jname_of_name n }

let print_shortname ff ({ Names.name = n } as qn) =
  Global_printer.print_shortname ff { qn with Names.name = jname_of_name n }

let java_print_string ff s =
  pp_print_string ff (jname_of_name s)

let class_name = print_qualname
let bare_class_name = print_shortname
let constructor_name = print_qualname
let bare_constructor_name = print_shortname
let method_name = java_print_string
let field_name = java_print_string
let const_name = print_qualname


let obj_ident = print_ident
let field_ident = print_ident
let var_ident = print_ident

let protection ff = function
  | Ppublic -> fprintf ff "public "
  | Pprotected -> fprintf ff "protected "
  | Pprivate -> fprintf ff "private "
  | Ppackage -> ()

let static ff s = if s then fprintf ff "static " else ()

let final ff f = if f then fprintf ff "final " else ()

let rec _ty is_new is_init ff t = match t with
  | Tbool -> fprintf ff "boolean"
  | Tint -> fprintf ff "int"
  | Tlong -> fprintf ff "long"
  | Tfloat -> fprintf ff "float"
  | Tclass n -> class_name ff n
  | Tgeneric (n, ty_l) ->
      if is_new
      then fprintf ff "%a" class_name n
      else fprintf ff "%a<@[%a@]>" class_name n (print_list_r ty """,""") ty_l
  | Tarray (t,s_l) ->
      let me = _ty is_new is_init in
      (* print size expressions only for new without init *)
      let print_size = if is_new && not is_init then exp else (fun _ff _e -> ()) in
      fprintf ff "%a@[%a@]" me t (print_list print_size "[""][""]") s_l
  | Tunit -> pp_print_string ff "void"

(* print types for [new] expressions (without generics) *)
and new_ty ff t = _ty true false ff t

(* print types for [new] expressions without generics nor array size *)
and new_init_ty ff t = _ty true true ff t

(* print types *)
and ty ff t = _ty false false ff t

and var_dec init ff vd =
  if init && not vd.vd_alias then
    fprintf ff "%a %a = %a" ty vd.vd_type var_ident vd.vd_ident exp (Java.default_value vd.vd_type)
  else
    fprintf ff "%a %a" ty vd.vd_type var_ident vd.vd_ident

and vd_list s1 s2 s3 ff vd_l = match vd_l with
  | [] -> ()
  | _ -> fprintf ff "@[<v>%a@]@\n" (print_list_r (var_dec true) s1 s2 s3) vd_l

and field ff f =
  fprintf ff "@[<2>%a%a%a%a %a%a@]"
    protection f.f_protection
    static f.f_static
    final f.f_final
    ty f.f_type
    field_ident f.f_ident
    (print_opt2 exp " = ") f.f_value

and exp ff = function
  | Ethis -> fprintf ff "this"
  | Efun (f,e_l) -> op ff (f, e_l)
  | Emethod_call (o,m,e_l) -> fprintf ff "%a.%a%a" exp o method_name m args e_l
  | Enew (c,e_l) -> fprintf ff "new %a%a" new_ty c args e_l
  | Enew_array (t,e_l) ->
    (match e_l with
      | [] -> fprintf ff "new %a" new_ty t
      | _ -> fprintf ff "new %a@[<2>%a@]" new_init_ty t (print_list_r exp "{"",""}") e_l )
  | Evoid -> ()
  | Ecast (t,e) -> fprintf ff "(%a)(%a)" ty t exp e
  | Svar c -> const_name ff c
  | Sint i -> pp_print_int ff i
  | Sfloat f -> fprintf ff "%Ff" f
  | Sbool b -> pp_print_bool ff b
  | Sconstructor c -> constructor_name ff c
  | Sstring s -> fprintf ff "\"%s\"" (String.escaped s)
  | Snull -> fprintf ff "null"
  | Efield (p,f) -> fprintf ff "%a.%a" exp p field_name f
  | Evar v -> var_ident ff v
  | Eclass c -> class_name ff c
  | Earray_elem (p,e_l) -> fprintf ff "%a@[%a@]" exp p (print_list exp "[""][""]") e_l

and op ff (f, e_l) =
  let javaop = function
    | "="  -> "=="
    | "<>" -> "!="
    | "or" -> "||"
    | "&"  -> "&&"
    | "*." -> "*"
    | "/." -> "/"
    | "+." -> "+"
    | "-." -> "-"
    | "~~" -> "~"
    | "<<<" -> "<<"
    | ">>>" -> ">>"
    | "&&&" -> "&"
    | "|||" -> "|"
    | op   -> op
  in
  match Names.modul f with
  | Names.Pervasives ->
      (match Names.shortname f with
        |("+" | "-" | "*" | "/" | "%"
        |"+." | "-." | "*." | "/."
        | "=" | "<>" | "<" | "<="
        | ">" | ">=" | "&" | "or") as n ->
           let e1,e2 = Misc.assert_2 e_l in
           fprintf ff "(@[%a@ %s %a@])" exp e1 (javaop n) exp e2
        | "not" ->
            let e = Misc.assert_1 e_l in
            fprintf ff "!%a" exp e
        | "~-" | "~-." ->
            let e = Misc.assert_1 e_l in
            fprintf ff "-%a" exp e
        | "=>" ->
           let e1,e2 = Misc.assert_2 e_l in
           fprintf ff "(@[!%a or %a@])" exp e1 exp e2
        | "assert" ->
            let e = Misc.assert_1 e_l in
            fprintf ff "assert(%a)" exp e
        | s -> fprintf ff "jeptagon.Pervasives.%s%a" s args e_l)
           (* TODO java deal with this correctly
            bug when using Pervasives.ggg in the code but works when using ggg directly *)
  | _ -> fprintf ff "%a%a" Global_printer.print_qualname f args e_l

and args ff e_l = fprintf ff "@[(%a)@]" (print_list_r exp """,""") e_l

and pattern ff = function
  | Pfield (p, f) -> fprintf ff "%a.%a" pattern p field_name f
  | Pvar v -> var_ident ff v
  | Pclass c -> class_name ff c
  | Parray_elem (p,e_l) -> fprintf ff "%a%a" pattern p (print_list exp "[""][""]") e_l
  | Pthis f -> fprintf ff "this.%a" field_ident f

let rec block ff b =
  fprintf ff "%a%a"
    (vd_list """;"";") b.b_locals
    (print_list_r act """""") b.b_body

(*
and switch_hack ff c_b_l =
  fprintf ff "@[<hv 2> default :
          \\Dead code. Hack to prevent \"may not be initialized\" java error.@ %a@ break;@]"
    block (c_b_l |> List.hd |> snd)
*)

and act ff = function
  | Anewvar (vd,e) -> fprintf ff "@[<4>%a =@ %a;@]" (var_dec false) vd exp e
  | Aassgn (p,e) -> fprintf ff "@[<4>%a =@ %a;@]" pattern p exp e
  | Aexp e -> fprintf ff "@[%a@];" exp e
  | Aswitch (e, c_b_l) ->
      let pcb ff (c,b) =
        let print_case ff c =
          match c with
          | Senum c -> bare_constructor_name ff c
          | Sexp e -> exp ff e in
        fprintf ff "@[<v4>case %a:@ %a@ break;@]" print_case c block b in
    (*  let switch_hack ff c_b_l = (* TODO java : better thing to do ? *)
        fprintf ff "@[<2>default ://Dead code. Hack to prevent \
                    \"may not be initialized\"
                    java error.@ %a@ break;@]" block (c_b_l |> List.hd |> snd)
      in*)
      fprintf ff "@[<v4>switch (%a) {@ %a@]@\n}"
        exp e
        (print_list_r pcb """""") c_b_l
  | Aif (e,bt) ->
      fprintf ff "@[<v 4>if (%a) {@ %a }@]" exp e block bt
  | Aifelse (e,bt,bf) ->
      fprintf ff "@[<v>@[<v4>if (%a) {@ %a@]@ @[<v4>} else {@ %a@]@ }@]"
        exp e
        block bt
        block bf
  | Ablock b -> if (List.length b.b_body > 0) then fprintf ff "@[<v>@[<v4>{@ %a@]@ }@]" block b
  | Afor (x, i1, i2, b) ->
      fprintf ff "@[<hv>@[<hv 4>for (%a = %a; %a<%a; %a++) {@ %a@]@ }@]"
        (var_dec false) x
        exp i1
        var_ident x.vd_ident
        exp i2
        var_ident x.vd_ident
        block b
  | Areturn e -> fprintf ff "return %a;" exp e

let methode ff m =
  fprintf ff "@[<v4>%a%a%a %a @[<4>(%a)@] @[%a@]{@ %a@]@\n}"
    protection m.m_protection
    static m.m_static
    ty m.m_returns
    method_name m.m_name
    (print_list_r (var_dec false) """,""") m.m_args
    (print_list_r class_name "throws "","" ") m.m_throws
    block m.m_body

let constructor ff m =
  fprintf ff "@[<v4>%a%a @[<4>(%a)@] {@\n%a@]@\n}"
    protection m.m_protection
    method_name m.m_name
    (print_list_r (var_dec false) """,""") m.m_args
    block m.m_body

let rec class_desc ff cd =
  fprintf ff "@[<v>%a@ %a@ %a@ %a@]"
    (print_list_r field """;"";") cd.cd_fields
    (print_list_r classe """""") cd.cd_classs
    (print_list constructor """""") cd.cd_constructors
    (print_list methode """""") cd.cd_methodes

and classe ff c = match c.c_kind with
  | Cenum c_l ->
      fprintf ff "@\n@[<4>%a%aenum %a {@\n%a@]@\n}"
        protection c.c_protection
        static c.c_static
        bare_class_name c.c_name
        (print_list_r bare_constructor_name """,""") c_l
  | Cgeneric cd ->
      fprintf ff "@\n@[<4>%a%aclass %a @[<h>%a@]{@\n%a@]@\n}"
        protection c.c_protection
        static c.c_static
        bare_class_name c.c_name
        (print_list_r class_name "implements "",""") c.c_implements
        class_desc cd

let output_classe base_dir c =
  let { Names.name = file_name; Names.qual = package } = c.c_name in
  let file_name = (jname_of_name file_name) ^ ".java" in
  let package_dirs = Misc.split_string (Names.modul_to_string package) "." in
  let create_dir base_dir dir =
    let dir = Filename.concat base_dir dir in
    Compiler_utils.ensure_dir dir;
    dir
  in
  let dir = List.fold_left create_dir base_dir package_dirs in
  let oc = open_out (Filename.concat dir file_name) in
  let ff = Format.formatter_of_out_channel oc in
  pp_set_margin ff 120;
  fprintf ff "package %a;@\n@[<v>%a@]@\n%a@."
    Global_printer.print_full_modul package
    (print_list_r (fun ff n -> fprintf ff "import %a" class_name n) """;"";") c.c_imports
    classe c;
  close_out oc

let output_program dir (p:Java.program) =
  List.iter (output_classe dir) p
