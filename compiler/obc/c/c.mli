(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(** Abstract syntax tree for C programs. *)
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
  | Cty_id of Names.qualname
      (** Previously defined C type, such as an enum or struct.*)
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

(** C expressions. *)
and cexpr =
  | Cuop of string * cexpr (** Unary operator with its name. *)
  | Cbop of string * cexpr * cexpr (** Binary operator. *)
  | Cfun_call of string * cexpr list (** Function call with its parameters. *)
  | Cconst of cconst (** Constants. *)
  | Clhs of clhs (** Left-hand-side expressions are obviously expressions! *)
  | Caddrof of clhs (** Take the address of a left-hand-side expression. *)
  | Cstructlit of string * cexpr list (** Structure literal [{f1, f2, ... }]. *)
  | Carraylit of cexpr list (** Array literal [\[e1, e2, ...\]]. *)
and cconst =
  | Ccint of int (** Integer constant. *)
  | Ccfloat of float (** Floating-point number constant. *)
  | Ctag of string (** Tag, member of a previously declared enumeration. *)
  | Cstrlit of string (** String literal, enclosed in double-quotes. *)
(** C left-hand-side (ie. affectable) expressions. *)
and clhs =
  | Cvar of string (** A local variable. *)
  | Cderef of clhs (** Pointer dereference, *ptr. *)
  | Cfield of clhs * Names.qualname (** Field access to left-hand-side. *)
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
  (** C typedef declaration (type, alias)*)
  | Cdecl_typedef of cty * string
  (** C enum declaration, with associated value tags. *)
  | Cdecl_enum of string * string list
  (** C structure declaration, with each field's name and type. *)
  | Cdecl_struct of string * (string * cty) list
  (** C function declaration. *)
  | Cdecl_function of string * cty * (string * cty) list

(** C function definition *)
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

val cdecl_of_cfundef : cdef -> cdecl

(** A C file can be a source file, containing definitions, or a header file,
    containing declarations. *)
type cfile_desc =
  | Cheader of string list * cdecl list (** Header dependencies * declaration
                                            list *)
  | Csource of cdef list

type cfile = string * cfile_desc (** File name * file content *)

(** [output dir cprog] pretty-prints the C program [cprog] to new files in the
    directory [dir]. *)
val output : string -> cfile list -> unit

(** [cname_of_name name] translates the string [name] to a valid C identifier.
    Copied verbatim from the old C backend. *)
val cname_of_name : string -> string
(** [cname_of_name q] translates the qualified name [q]
    to a valid C identifier. *)
val cname_of_qn : Names.qualname -> string

(** Converts an expression to a lhs. *)
val lhs_of_exp : cexpr -> clhs

(** Returns the type of a pointer to a type, except for
    types which are already pointers. *)
val pointer_to : cty -> cty

(** Returns whether a type is a pointer. *)
val is_pointer_type : cty -> bool

(** [array_base_ctype ty idx_list] returns the base type of an array
    type. If idx_list = [i1; ..; ip] and a is a variable of type ty,
    then it returns a[i1]..[ip]. *)
val array_base_ctype : cty -> int list -> cty


