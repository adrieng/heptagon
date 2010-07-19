(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Format
open List
open Modules


let rec print_list ff print sep l =
  match l with
    | [] -> ()
    | [x] -> print ff x
    | x :: l ->
        print ff x;
        fprintf ff "%s@ " sep;
        print_list ff print sep l

(** [cname_of_name name] translates the string [name] to a valid C identifier.
    Copied verbatim from the old C backend. *)
let cname_of_name name =
  let buf = Buffer.create (String.length name) in
  let rec convert c =
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
  | Cty_id of string (** Previously defined C type, such as an enum or struct.*)
  | Cty_ptr of cty (** C points-to-other-type type. *)
  | Cty_arr of int * cty (** A static array of the specified size. *)
  | Cty_void (** Well, [void] is not really a C type. *)

(** A C block: declarations and statements. In source code form, it begins with
    variable declarations before a list of semicolon-separated statements, the
    whole thing being enclosed in curly braces. *)
type cblock = {
  (** Variable declarations, where each declaration consists of a variable
      name and the associated C type. *)
  var_decls : (string * cty) list;
  (** The actual statement forming our block. *)
  block_body : cstm list;
}

(* TODO: The following types for C expressions would be better using polymorphic
   variants to define LHS expressions as a proper superset of general
   expressions. *)

(** C expressions. *)
and cexpr =
  | Cuop of string * cexpr (** Unary operator with its name. *)
  | Cbop of string * cexpr * cexpr (** Binary operator. *)
  | Cfun_call of string * cexpr list (** Function call with its parameters. *)
  | Cconst of cconst (** Constants. *)
  | Clhs of clhs (** Left-hand-side expressions are obviously expressions! *)
  | Caddrof of clhs (** Take the address of a left-hand-side expression. *)
  | Cstructlit of string * cexpr list (** Structure literal "{ f1, f2, ... }".*)
  | Carraylit of cexpr list (** Array literal [e1, e2, ...]. *)
and cconst =
  | Ccint of int (** Integer constant. *)
  | Ccfloat of float (** Floating-point number constant. *)
  | Ctag of string (** Tag, member of a previously declared enumeration. *)
  | Cstrlit of string (** String literal, enclosed in double-quotes. *)
      (** C left-hand-side (ie. affectable) expressions. *)
and clhs =
  | Cvar of string (** A local variable. *)
  | Cderef of clhs (** Pointer dereference, *ptr. *)
  | Cfield of clhs * string (** Field access to left-hand-side. *)
  | Carray of clhs * cexpr (** Array access clhs[cexpr] *)
      (** C statements. *)
and cstm =
  | Csexpr of cexpr (** Expression evaluation, may cause side-effects! *)
  | Csblock of cblock (** A local sub-block, can have its own private decls. **)
  | Cskip (** A dummy instruction that does nothing and will not be printed. *)
  | Caffect of clhs * cexpr (** Affect the result of an expression to a lhs. *)
  | Cif of cexpr * cstm list * cstm list (** Alternative *)
  | Cswitch of cexpr * (string * cstm list) list (** Case/switch over an enum.*)
  | Cwhile of cexpr * cstm list (** While loop. *)
  | Cfor of string * int * int * cstm list (** For loop. int <= string < int *)
  | Creturn of cexpr (** Ends a procedure/function by returning an expression.*)

(** C type declarations ; will {b always} correspond to a typedef in emitted
    source code. *)
type cdecl =
    (** C enum declaration, with associated value tags. *)
  | Cdecl_enum of string * string list
    (** C structure declaration, with each field's name and type. *)
  | Cdecl_struct of string * (string * cty) list
    (** C function declaration. *)
  | Cdecl_function of string * cty * (string * cty) list

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
  | [] -> fprintf fmt ""
  | [x] -> fprintf fmt "%a" f x
  | h :: t -> fprintf fmt "%a%s@ %a" f h sep (pp_list1 f sep) t

let rec pp_list f sep fmt l = match l with
  | [] -> fprintf fmt ""
  | h :: t -> fprintf fmt "@ %a%s%a" f h sep (pp_list f sep) t

let pp_string fmt s =
  fprintf fmt "%s" (cname_of_name s)

let rec pp_cty fmt cty = match cty with
  | Cty_int -> fprintf fmt "int"
  | Cty_float -> fprintf fmt "float"
  | Cty_char -> fprintf fmt "char"
  | Cty_id s -> pp_string fmt s
  | Cty_ptr cty' -> fprintf fmt "%a*" pp_cty cty'
  | Cty_arr (n, cty') -> fprintf fmt "%a[%d]" pp_cty cty' n
  | Cty_void -> fprintf fmt "void"

(** [pp_array_decl cty] returns the base type of a (multidimensionnal) array
    and the string of indices. *)
let rec pp_array_decl cty =
  match cty with
    | Cty_arr(n, cty') ->
        let ty, s = pp_array_decl cty' in
        ty, sprintf "%s[%d]" s n
    | _ -> cty, ""

let rec pp_param_cty fmt = function
    | Cty_arr(n, cty') ->
          fprintf fmt "%a*" pp_param_cty cty'
    | cty -> pp_cty fmt cty

(* pp_vardecl, featuring an ugly hack coping with C's inconsistent concrete
   syntax! *)
let rec pp_vardecl fmt (s, cty) = match cty with
  | Cty_arr (n, cty') ->
      let ty, indices = pp_array_decl cty in
      fprintf fmt "%a %a%s" pp_cty ty  pp_string s indices
  | _ -> fprintf fmt "%a %a" pp_cty cty  pp_string s
and pp_paramdecl fmt (s, cty) = match cty with
  | Cty_arr (n, cty') -> fprintf fmt "%a* %a" pp_param_cty cty'  pp_string s
  | _ -> pp_vardecl fmt (s, cty)
and pp_param_list fmt l = pp_list1 pp_paramdecl "," fmt l
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
      fprintf fmt "@[<v>@[<v 2>switch (%a) {%a@]@ }@]"
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
      fprintf fmt "@[<v>@[<v 2>for (int %a = %d; %a < %d; ++%a) {%a@]@ }@]"
        pp_string x  lower  pp_string x
        upper  pp_string x  pp_cstm_list e
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
  | Cconst (Ccint i) -> fprintf fmt "%d" i
  | Cconst (Ccfloat f) -> fprintf fmt "%f" f
  | Cconst (Ctag "true") -> fprintf fmt "TRUE"
  | Cconst (Ctag "false") -> fprintf fmt "FALSE"
  | Cconst (Ctag t) -> pp_string fmt t
  | Cconst (Cstrlit t) -> fprintf fmt "\"%s\"" t
  | Clhs lhs -> fprintf fmt "%a" pp_clhs lhs
  | Caddrof lhs -> fprintf fmt "&%a" pp_clhs lhs
  | Cstructlit (s, el) ->
      fprintf fmt "(%a){@[%a@]}" pp_string s (pp_list1 pp_cexpr ",") el
  | Carraylit el ->
      fprintf fmt "((int []){@[%a@]})" (pp_list1 pp_cexpr ",") el (* WRONG *)
and pp_clhs fmt lhs = match lhs with
  | Cvar s -> pp_string fmt s
  | Cderef lhs' -> fprintf fmt "*%a" pp_clhs lhs'
  | Cfield (Cderef lhs, f) -> fprintf fmt "%a->%a" pp_clhs lhs  pp_string f
  | Cfield (lhs, f) -> fprintf fmt "%a.%s" pp_clhs lhs f
  | Carray (lhs, e) ->
      fprintf fmt "%a[%a]"
        pp_clhs lhs
        pp_cexpr e

let pp_cdecl fmt cdecl = match cdecl with
  | Cdecl_enum (s, sl) ->
      fprintf fmt "@[<v>@[<v 2>typedef enum {@ %a@]@ } %a;@ @]@\n"
        (pp_list1 pp_string ",") sl  pp_string s
  | Cdecl_struct (s, fl) ->
      let pp_field fmt (s, cty) =
        fprintf fmt "@ %a;" pp_vardecl (s,cty) in
      fprintf fmt "@[<v>@[<v 2>typedef struct %a {"  pp_string s;
      List.iter (pp_field fmt) fl;
      fprintf fmt "@]@ } %a;@ @]@\n"  pp_string s
  | Cdecl_function (n, retty, args) ->
      fprintf fmt "@[<v>%a %a(@[<hov>%a@]);@ @]@\n"
        pp_cty retty  pp_string n  pp_param_list args

let pp_cdef fmt cdef = match cdef with
  | Cfundef cfd ->
      fprintf fmt
        "@[<v>@[<v 2>%a %a(@[<hov>%a@]) {%a@]@ }@ @]@\n"
        pp_cty cfd.f_retty  pp_string cfd.f_name  pp_param_list cfd.f_args
        pp_cblock cfd.f_body
  | Cvardef (s, cty) -> fprintf fmt "%a %a;@\n" pp_cty cty  pp_string s

let pp_cfile_desc fmt filen cfile =
  (** [filen_wo_ext] is the file's name without the extension. *)
  let filen_wo_ext = String.sub filen 0 (String.length filen - 2) in
  match cfile with
    | Cheader (deps, cdecls) ->
        let headern_macro = String.uppercase filen_wo_ext in
        Misc.print_header_info fmt "/*" "*/";
        fprintf fmt "#ifndef %s_H@\n" headern_macro;
        fprintf fmt "#define %s_H@\n@\n" headern_macro;
        (* fprintf fmt "#include \"types.h\"\n"; *)
        iter (fun d -> fprintf fmt "#include \"%s.h\"@\n" d)
          deps;
        iter (pp_cdecl fmt) cdecls;
        fprintf fmt "#endif // %s_H@\n" headern_macro
    | Csource cdefs ->
        let headern = filen_wo_ext ^ ".h" in
        Misc.print_header_info fmt "/*" "*/";
        fprintf fmt "#include <stdio.h>@\n";
        fprintf fmt "#include <string.h>@\n";
        fprintf fmt "#include <stdlib.h>@\n";
        fprintf fmt "#include \"%s\"@\n@\n" headern;
        fprintf fmt "#define FALSE 0@\n#define TRUE 1@\n@\n";
        iter (pp_cdef fmt) cdefs

(******************************)

(** [output_cfile dir cfile] pretty-prints the content of [cfile] to the
    corresponding file in the [dir] directory. *)
let output_cfile dir (filen, cfile_desc) =
  if !Misc.verbose then Printf.printf "C-NG generating %s/%s\n" dir filen;
  let buf = Buffer.create 20000 in
  let oc = open_out (Filename.concat dir filen) in
  let fmt = Format.formatter_of_buffer buf in
  pp_cfile_desc fmt filen cfile_desc;
  Buffer.output_buffer oc buf;
  close_out oc

let output dir cprog =
  List.iter (output_cfile dir) cprog

(** { Lexical conversions to C's syntax } *)

(** Converts an expression to a lhs. *)
let lhs_of_exp e =
  match e with
    | Clhs e -> e
    | _ -> assert false

(** Returns the type of a pointer to a type, except for
    types which are already pointers. *)
let pointer_to ty =
  match ty with
    | Cty_arr _ | Cty_ptr _ -> ty
    | _ -> Cty_ptr ty

(** Returns whether a type is a pointer. *)
let is_pointer_type = function
  | Cty_arr _ | Cty_ptr _ -> true
  | _ -> false

(** [array_base_ctype ty idx_list] returns the base type of an array
    type. If idx_list = [i1; ..; ip] and a is a variable of type ty,
    then it returns a[i1]..[ip]. *)
let rec array_base_ctype ty idx_list =
  match ty, idx_list with
    | Cty_arr (n, ty), [i] -> ty
    | Cty_arr (n, ty), i::idx_list -> array_base_ctype ty idx_list
    | _ -> assert false
