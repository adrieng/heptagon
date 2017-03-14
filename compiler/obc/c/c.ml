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

open Format
open List
open Names

let print_list ff print sep l = Pp_tools.print_list_r print "" sep "" ff l

(** [cname_of_name name] translates the string [name] to a valid C identifier.
    Copied verbatim from the old C backend. *)
let cname_of_name name =
  let buf = Buffer.create (String.length name) in
  let convert c =
    match c with
      | 'A'..'Z' | 'a'..'z' | '0'..'9' | '_' ->
          Buffer.add_char buf c
      | '\'' -> Buffer.add_string buf "_prime"
      | _ ->
          Buffer.add_string buf "lex";
          Buffer.add_string buf (string_of_int (Char.code c));
          Buffer.add_string buf "_" in
  String.iter convert name;
  Buffer.contents buf

(******************************)

(** {2 C abstract syntax tree } *)

(** Here is the C abstract syntax tree used by MiniLS for its C backend. It does
    not try to completly model the C language, only the relatively small part
    that were are interested in (e.g. no function pointers or local variable
    initialization). *)

(** C types relevant for Obc. Note the absence of function pointers. *)
type cty =
  | Cty_int (** C machine-dependent integer type. *)
  | Cty_float (** C machine-dependent single-precision floating-point type. *)
  | Cty_char (** C character type. *)
  | Cty_id of qualname
  (** Previously defined C type, such as an enum or struct.*)
  | Cty_ptr of cty (** C points-to-other-type type. *)
  | Cty_arr of int * cty (** A static array of the specified size. *)
  | Cty_void (** Well, [void] is not really a C type. *)

(** A C block: declarations and statements. In source code form, it begins with
    variable declarations before a list of semicolon-separated statements, the
    whole thing being enclosed in curly braces. *)
type cblock = {
  var_decls : (string * cty) list;
  (** Variable declarations, where each declaration consists of a variable
      name and the associated C type. *)
  block_body : cstm list;
  (** The actual statement forming our block. *)
}

(* TODO: The following types for C expressions would be better using polymorphic
   variants to define LHS expressions as a proper superset of general
   expressions. *)

(** C expressions. *)
and cexpr =
  | Cuop of string * cexpr (** Unary operator with its name. *)
  | Cbop of string * cexpr * cexpr (** Binary operator. *)
  | Cfun_call of string * cexpr list (** Function call with its parameters. *)
  | Caddrof of cexpr (** Take the address of an expression. *)
  | Cstructlit of string * cexpr list (** Structure literal [{ f1, f2, ... }].*)
  | Carraylit of cexpr list (** Array literal [\[e1, e2, ...\]]. *)
  | Cconst of cconst (** Constants. *)
  | Cvar of string (** A local variable. *)
  | Cderef of cexpr (** Pointer dereference, *ptr. *)
  | Cfield of cexpr * qualname (** Field access to left-hand-side. *)
  | Carray of cexpr * cexpr (** Array access cexpr[cexpr] *)

and cconst =
  | Ccint of int (** Integer constant. *)
  | Ccfloat of float (** Floating-point number constant. *)
  | Ctag of string (** Tag, member of a previously declared enumeration. *)
  | Cstrlit of string (** String literal, enclosed in double-quotes. *)

(** C left-hand-side (ie. affectable) expressions. *)
and clhs =
  | CLvar of string (** A local variable. *)
  | CLderef of clhs (** Pointer dereference, *ptr. *)
  | CLfield of clhs * qualname (** Field access to left-hand-side. *)
  | CLarray of clhs * cexpr (** Array access clhs[cexpr] *)

(** C statements. *)
and cstm =
  | Csexpr of cexpr (** Expression evaluation, may cause side-effects! *)
  | Csblock of cblock (** A local sub-block, can have its own private decls. **)
  | Cskip (** A dummy instruction that does nothing and will not be printed. *)
  | Caffect of clhs * cexpr (** Affect the result of an expression to a lhs. *)
  | Cif of cexpr * cstm list * cstm list (** Alternative *)
  | Cswitch of cexpr * (string * cstm list) list (** Case/switch over an enum.*)
  | Cwhile of cexpr * cstm list (** While loop. *)
  | Cfor of string * cexpr * cexpr * cstm list (** For loop. int <= string < int *)
  | Creturn of cexpr (** Ends a procedure/function by returning an expression.*)

(** C type declarations ; will {b always} correspond to a typedef in emitted
    source code. *)
type cdecl =
  | Cdecl_typedef of cty * string
  (** C typedef declaration (alias, name)*)
  | Cdecl_enum of string * string list
  (** C enum declaration, with associated value tags. *)
  | Cdecl_struct of string * (string * cty) list
  (** C structure declaration, with each field's name and type. *)
  | Cdecl_function of string * cty * (string * cty) list
  (** C function declaration. *)
  | Cdecl_constant of string * cty * cexpr
  (** C constant declaration (alias, name)*)

(** C function definitions *)
type cfundef = {
  f_name : string; (** The function's name. *)
  f_retty : cty; (** The function's return type. *)
  f_args : (string * cty) list; (** Each parameter's name and type. *)
  f_body : cblock; (** Actual instructions, in the form of a block. *)
}

(** C top-level definitions. *)
type cdef =
  | Cfundef of cfundef (** Function definition, see [cfundef]. *)
  | Cvardef of string * cty (** A variable definition, with its name and type.*)

(** [cdecl_of_cfundef cfd] returns a declaration for the function def. [cfd]. *)
let cdecl_of_cfundef cfd = match cfd with
  | Cfundef cfd -> Cdecl_function (cfd.f_name, cfd.f_retty, cfd.f_args)
  | _ -> invalid_arg "cdecl_of_cfundef"

(** A C file can be a source file, containing definitions, or a header file,
    containing declarations. *)
type cfile = string * cfile_desc
and cfile_desc =
  | Cheader of string list * cdecl list (** Header dependencies * declaration
                                            list *)
  | Csource of cdef list

(******************************)

(** {3 Pretty-printing of the C ast.} *)

(** [pp_list1 f sep fmt l] pretty-prints into the Format.formatter [fmt]
    elements of the list [l] via the function [f], separated by [sep] strings
    and breakable spaces. *)
let rec pp_list1 f sep fmt l = match l with
  | [] -> ()
  | [x] -> fprintf fmt "%a" f x
  | h :: t -> fprintf fmt "%a%s@ %a" f h sep (pp_list1 f sep) t

let rec pp_list f sep fmt l = match l with
  | [] -> ()
  | h :: t -> fprintf fmt "@ %a%s%a" f h sep (pp_list f sep) t

let pp_string fmt s =
  fprintf fmt "%s" (cname_of_name s)

let rec modul_to_cname q = match q with
  | Pervasives | LocalModule -> ""
  | Module m -> m ^ "__"
  | QualModule { qual = q; name = n } ->
      (modul_to_cname q)^n^"__"

let cname_of_qn qn =
  (modul_to_cname qn.qual) ^ qn.name

let pp_qualname fmt q =
  pp_string fmt (cname_of_qn q)

let pp_shortname fmt q =
  pp_string fmt q.name

let rec pp_cty fmt cty = match cty with
  | Cty_int -> fprintf fmt "int"
  | Cty_float -> fprintf fmt "float"
  | Cty_char -> fprintf fmt "char"
  | Cty_id s -> pp_qualname fmt s
  | Cty_ptr cty' -> fprintf fmt "%a*" pp_cty cty'
  | Cty_arr (n, cty') -> fprintf fmt "%a[%d]" pp_cty cty' n
  | Cty_void -> fprintf fmt "void"

(** [pp_array_decl cty] returns the base type of a (multidimensionnal) array
    and the string of indices. *)
let rec pp_array_decl cty =
  match cty with
    | Cty_arr(n, cty') ->
        let ty, s = pp_array_decl cty' in
        ty, sprintf "[%d]%s" n s
    | _ -> cty, ""

let rec pp_param_cty fmt = function
    | Cty_arr(_, cty') ->
          fprintf fmt "%a*" pp_param_cty cty'
    | cty -> pp_cty fmt cty

(* pp_vardecl, featuring an ugly hack coping with C's inconsistent concrete
   syntax! *)
let rec pp_vardecl fmt (s, cty) = match cty with
  | Cty_arr _ ->
      let ty, indices = pp_array_decl cty in
      fprintf fmt "%a %a%s" pp_cty ty  pp_string s indices
  | _ -> fprintf fmt "%a %a" pp_cty cty  pp_string s
and pp_param_list fmt l = pp_list1 pp_vardecl "," fmt l
and pp_var_list fmt l = pp_list pp_vardecl ";" fmt l

let rec pp_cblock fmt cb =
  let pp_varlist = pp_list pp_vardecl ";" in
  fprintf fmt "%a%a" pp_varlist cb.var_decls pp_cstm_list cb.block_body
and pp_cstm_list fmt stml = pp_list pp_cstm ";" fmt stml
and pp_cstm fmt stm = match stm with
  | Csexpr e -> fprintf fmt "%a" pp_cexpr e
  | Cswitch (e, cl) ->
      let pp_clause fmt (tag, stml) =
        fprintf fmt "@[<v 2>case %a:%a@ break;@]"
          pp_cexpr (Cconst (Ctag tag)) pp_cstm_list stml in
      fprintf fmt
        "@[<v>@[<v 2>switch (%a) {%a@ @[<v 2>default:@ break;@]@]@ }@]"
        pp_cexpr e (pp_list pp_clause "") cl
  | Caffect (lhs, e) ->
      fprintf fmt "%a = %a" pp_clhs lhs pp_cexpr e
  | Cif (c, t, []) ->
      fprintf fmt "@[<v>@[<v 2>if (%a) {%a@]@ }@]"
        pp_cexpr c pp_cstm_list t
  | Cif (c, t, e) ->
      fprintf fmt "@[<v>@[<v 2>if (%a) {%a@]@ @[<v 2>} else {%a@]@ }@]"
        pp_cexpr c pp_cstm_list t pp_cstm_list e
  | Cfor(x, lower, upper, e) ->
      fprintf fmt
        "@[<v>@[<v 2>{@\nint %a;@\n@[<v 2>for (%a = %a; %a < %a; ++%a) {%a@]@ }@]@\n}@]"
        pp_string x
        pp_string x  pp_cexpr lower  pp_string x
        pp_cexpr upper  pp_string x  pp_cstm_list e
  | Cwhile (e, b) ->
      fprintf fmt "@[<v>@[<v 2>while (%a) {%a@]@ }@]" pp_cexpr e pp_cstm_list b
  | Csblock cb -> pp_cblock fmt cb
  | Cskip -> fprintf fmt ""
  | Creturn e -> fprintf fmt "return %a" pp_cexpr e
and pp_cexpr fmt ce = match ce with
  | Cuop (s, e) -> fprintf fmt "%s(%a)" s  pp_cexpr e
  | Cbop (s, l, r) -> fprintf fmt "(%a%s%a)" pp_cexpr l s pp_cexpr r
  | Cfun_call (s, el) ->
      fprintf fmt "%a(@[%a@])"  pp_string s  (pp_list1 pp_cexpr ",") el
  | Caddrof (Cderef e) -> pp_cexpr fmt e
  | Cderef (Caddrof e) -> pp_cexpr fmt e
  | Caddrof e -> fprintf fmt "&%a" pp_cexpr e
  | Cstructlit (s, el) ->
      fprintf fmt "(%a){@[%a@]}" pp_string s (pp_list1 pp_cexpr ",") el
  | Carraylit el -> (* TODO master : WRONG *)
      fprintf fmt "((int []){@[%a@]})" (pp_list1 pp_cexpr ",") el
  | Cconst c -> pp_cconst fmt c
  | Cvar s -> pp_string fmt s
  | Cderef e -> fprintf fmt "*%a" pp_cexpr e
  | Cfield (Cderef e, f) -> fprintf fmt "%a->%a" pp_cexpr e pp_shortname f
  | Cfield (e, f) -> fprintf fmt "%a.%a" pp_cexpr e pp_shortname f
  | Carray (e1, e2) -> fprintf fmt "%a[%a]" pp_cexpr e1 pp_cexpr e2

and pp_cconst_expr fmt ce = match ce with
  | Cstructlit (_, el) ->
      fprintf fmt "{@[%a@]}" (pp_list1 pp_cconst_expr ",") el
  | Carraylit el ->
      fprintf fmt "{@[%a@]}" (pp_list1 pp_cconst_expr ",") el
  | _ -> pp_cexpr fmt ce

and pp_clhs fmt clhs = match clhs with
  | CLvar s -> pp_string fmt s
  | CLderef lhs' -> fprintf fmt "*%a" pp_clhs lhs'
  | CLfield (CLderef lhs, f) -> fprintf fmt "%a->%a" pp_clhs lhs  pp_shortname f
  | CLfield (lhs, f) -> fprintf fmt "%a.%a" pp_clhs lhs  pp_shortname f
  | CLarray (lhs, e) ->
      fprintf fmt "%a[%a]"
        pp_clhs lhs
        pp_cexpr e

and pp_cconst fmt cconst = match cconst with
  | Ccint i -> fprintf fmt "%d" i
  | Ccfloat f -> fprintf fmt "%f" f
  | Ctag t -> pp_string fmt t
  | Cstrlit t -> fprintf fmt "\"%s\"" (String.escaped t)

let pp_cdecl fmt cdecl = match cdecl with
  | Cdecl_enum (s, sl) ->
      fprintf fmt "@[<v>@[<v 2>typedef enum {@ %a@]@ } %a;@ @]@\n"
        (pp_list1 pp_string ",") sl  pp_string s
  | Cdecl_typedef (cty, n) ->
      fprintf fmt "@[<v>@[<v 2>typedef %a;@ @]@\n"
        pp_vardecl (n, cty)
  | Cdecl_struct (s, fl) ->
      let pp_field fmt (s, cty) =
        fprintf fmt "@ %a;" pp_vardecl (s,cty) in
      fprintf fmt "@[<v>@[<v 2>typedef struct %a {"  pp_string s;
      List.iter (pp_field fmt) fl;
      fprintf fmt "@]@ } %a;@ @]@\n"  pp_string s
  | Cdecl_function (n, retty, args) ->
      fprintf fmt "@[<v>%a %a(@[<hov>%a@]);@ @]@\n"
        pp_cty retty  pp_string n  pp_param_list args
  | Cdecl_constant (n, cty, ce) ->
      fprintf fmt "@[<v>static const %a = %a;@ @]@\n"
        pp_vardecl (n, cty)  pp_cconst_expr ce

let pp_cdef fmt cdef = match cdef with
  | Cfundef cfd ->
      fprintf fmt
        "@[<v>@[<v 2>%a %a(@[<hov>%a@]) {%a@]@ }@ @]@\n"
        pp_cty cfd.f_retty  pp_string cfd.f_name  pp_param_list cfd.f_args
        pp_cblock cfd.f_body
  | Cvardef (s, cty) -> fprintf fmt "%a %a;@\n" pp_cty cty  pp_string s

let pp_cfile_desc fmt filen cfile =
  (* [filen_wo_ext] is the file's name without the extension. *)
  let filen_wo_ext = String.sub filen 0 (String.length filen - 2) in
  match cfile with
    | Cheader (deps, cdecls) ->
        let headern_macro = String.uppercase_ascii filen_wo_ext in
        Compiler_utils.print_header_info fmt "/*" "*/";
        fprintf fmt "#ifndef %s_H@\n" headern_macro;
        fprintf fmt "#define %s_H@\n@\n" headern_macro;
        iter (fun d -> fprintf fmt "#include \"%s.h\"@\n" d)
          deps;
        iter (pp_cdecl fmt) cdecls;
        fprintf fmt "#endif // %s_H@\n@?" headern_macro
    | Csource cdefs ->
        let headern = filen_wo_ext ^ ".h" in
        Compiler_utils.print_header_info fmt "/*" "*/";
        fprintf fmt "#include <stdio.h>@\n";
        fprintf fmt "#include <string.h>@\n";
        fprintf fmt "#include <stdlib.h>@\n";
        fprintf fmt "#include \"%s\"@\n@\n" headern;
        iter (pp_cdef fmt) cdefs

(******************************)

(** [output_cfile dir cfile] pretty-prints the content of [cfile] to the
    corresponding file in the [dir] directory. *)
let output_cfile dir (filen, cfile_desc) =
  if !Compiler_options.verbose then
    Format.printf "C-NG generating %s/%s@." dir filen;
  let oc = open_out (Filename.concat dir filen) in
  let fmt = Format.formatter_of_out_channel oc in
  pp_cfile_desc fmt filen cfile_desc;
  pp_print_flush fmt ();
  close_out oc

let output dir cprog =
  List.iter (output_cfile dir) cprog

(** Returns whether a type is a pointer. *)
let is_pointer_type = function
  | Cty_arr _ | Cty_ptr _ -> true
  | _ -> false

(** [array_base_ctype ty idx_list] returns the base type of an array
    type. If idx_list = [i1; ..; ip] and a is a variable of type ty,
    then it returns a[i1]..[ip]. *)
let rec array_base_ctype ty idx_list =
  match ty, idx_list with
    | Cty_arr (_, ty), [_] -> ty
    | Cty_arr (_, ty), _::idx_list -> array_base_ctype ty idx_list
    | _ ->
      assert false

(** Convert C expression to left-hand side *)
let rec clhs_of_cexpr cexpr =
  match cexpr with
  | Cvar v -> CLvar v
  | Cderef e -> CLderef (clhs_of_cexpr e)
  | Cfield (e,qn) -> CLfield (clhs_of_cexpr e, qn)
  | Carray (e1,e2) -> CLarray (clhs_of_cexpr e1, e2)
  | _ -> failwith("C expression not translatable to LHS")
