(**************************************************************************)
(*                                                                        *)
(*  Lucid Synchrone                                                       *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* $Id: caml_printer.ml,v 1.20 2008-06-17 13:21:12 pouzet Exp $ *)

(** Printing [Caml] code *)

open Misc
open Names
open Format
open Declarative
open Declarative_printer
open Caml

(** Generic printing of a list.
    This function seems to appear in several places... *)
let print_list print print_sep l =
  let rec printrec l =
    match l with
      [] -> ()
    | [x] ->
  print x
    | x::l ->
  open_box 0;
  print x;
  print_sep ();
  print_space ();
  printrec l;
  close_box () in
  printrec l

(** Prints an immediate. A patch is needed on float number for
    [ocaml] < 3.05. *)
let print_immediate i =
  match i with
    Cbool(b) -> print_string (if b then "true" else "false")
  | Cint(i) -> print_int i
  | Cfloat(f) ->  print_float f
  | Cchar(c) -> print_char '\''; print_char c; print_char '\''
  | Cstring(s) -> print_string "\"";
                  print_string (String.escaped s);
      print_string "\""
  | Cvoid -> print_string "()"

(** Prints a name. Infix chars are surrounded by parenthesis *)
let is_infix =
  let module StrSet = Set.Make(String) in
  let set_infix =
    List.fold_right
      StrSet.add
      ["or"; "quo"; "mod"; "land"; "lor"; "lxor"; "lsl"; "lsr"; "asr"]
      StrSet.empty in
  fun s -> StrSet.mem s set_infix

let print_name s =
  let c = String.get s 0 in
  let s = if is_infix s then "(" ^ s ^ ")"
          else match c with
    | 'a' .. 'z' | 'A' .. 'Z' | '_' | '`' -> s
          | '*' -> "( " ^ s ^ " )"
          | _ -> if s = "()" then s else "(" ^ s ^ ")" in
  print_string s

(** Prints a global name *)
let print_qualified_ident {qual=q;id=n} =
  (* special case for values imported from the standard library *)
  if (q = pervasives_module) or (q = Modules.compiled_module_name ())
     or (q = "")
  then print_name n
  else
    begin
      print_string q;
      print_string ".";
      print_name n
    end

let priority exp =
  match exp with
    Crecord _ | Crecord_access _ | Cvar _ | Ctuple _
  | Cglobal _ | Cconstant _ | Cconstruct(_, []) | Cderef _ -> 3
  | Clet _ | Cfun _ | Cseq _ -> 1
  | Cset _ | Clabelset _
  | Cref _ | Capply _ | Cmagic _ | Cconstruct _ -> 2
  | Cifthen _ | Cifthenelse _ | Cmatch _ -> 0

let priority_pattern p =
  match p with
    Cconstructpat _ | Cconstantpat _ | Cvarpat _
  | Ctuplepat _ | Crecordpat _ -> 2
  | _ -> 1

(** Emission of code *)
let rec print pri e =
  open_box 2;
  (* if the priority of the context is higher than the *)
  (* priority of e, we ass a parenthesis *)
  let pri_e = priority e in
  if pri > pri_e then print_string "(";
  begin match e with
    Cconstant(e) -> print_immediate e
  | Cglobal(gl) -> print_qualified_ident gl
  | Cvar(s) -> print_name s
  | Cconstruct(gl, e_list) ->
      print_qualified_ident gl;
      if e_list <> [] then print_tuple e_list
  | Capply(f,l) ->
      print pri_e f;
      print_space ();
      print_list (print (pri_e + 1)) (fun () -> ()) l
  | Cfun(pat_list,e) ->
      print_string "fun";
      print_space ();
      print_list (print_pattern 0) (fun () -> ()) pat_list;
      print_space ();
      print_string "->";
      print_space ();
      print 0 e
  (* local definition *)
  | Clet(is_rec, l, e) -> print_let is_rec l e
  | Cifthenelse(e1,e2,e3) ->
      print_string "if";
      print_space ();
      print (pri_e - 1) e1;
      print_space ();
      print_string "then";
      print_space ();
      print 2 e2;
      print_space ();
      print_string "else";
      print_space ();
      print 2 e3
  | Cifthen(e1,e2) ->
      print_string "if";
      print_space ();
      print (pri_e - 1) e1;
      print_space ();
      print_string "then";
      print_space ();
      print 2 e2
  | Ctuple(l) -> print_tuple l
  | Crecord(l) ->
      print_string "{";
      print_list
  (fun (gl, e) -> print_qualified_ident gl;
          print_string " = ";
    print 1 e)
        (fun () -> print_string ";") l;
      print_string "}"
  | Crecord_access(e, gl) ->
      print pri_e e;
      print_string ".";
      print_qualified_ident gl
  | Cmatch(e,l) ->
      print_string "match ";
      print 0 e;
      print_string " with";
      print_space ();
      List.iter
  (fun pat_expr ->
    print_string "| ";
    print_match_pat_expr 2 pat_expr) l
  | Cseq l -> print_list (print 2) (fun () -> print_string ";") l
  | Cderef(e) ->
      print_string "!";
      print pri_e e
  | Cref(e) ->
      print_string "ref";
      print_space ();
      print (pri_e + 1) e
  | Cset(s, e) ->
      print_string s;
      print_string " :=";
      print_space ();
      print pri_e e
  | Clabelset(s, l, e) ->
      print_string s;
      print_string ".";
      print_string l;
      print_space ();
      print_string "<-";
      print_space ();
      print pri_e e
  | Cmagic(e) ->
      print_string "Obj.magic";
      print_space ();
      print (pri_e+1) e
  end;
  if pri > pri_e then print_string ")";
  close_box()

and print_tuple e_list =
  print_string "(";
  print_list (print 2) (fun () -> print_string ",") e_list;
  print_string ")"

and print_let_pat_expr (pat, expr) =
  match pat, expr with
      pat, Cfun(pat_list, expr) ->
  open_box 2;
  print_list (print_pattern 0) (fun () -> ()) (pat :: pat_list);
  print_string " =";
  print_space ();
  print 0 expr;
  close_box ()
    | _ ->
  print_pattern 0 pat;
  print_string " = ";
  print 0 expr

and print_let is_rec l e =
  open_box 0;
  if is_rec then print_string "let rec " else print_string "let ";
  print_list print_let_pat_expr
    (fun () -> print_string "\n"; print_string "and ") l;
  print_string " in";
  print_break 1 0;
  print 0 e;
  close_box ()

and print_pattern pri pat =
  open_box 2;
  let pri_e = priority_pattern pat in
  if pri > pri_e then print_string "(";
  begin match pat with
    Cconstantpat(i) -> print_immediate i
  | Cvarpat(v) -> print_string v
  | Cconstructpat(gl, pat_list) ->
      print_qualified_ident gl;
      if pat_list <> [] then print_tuple_pat pat_list
  | Ctuplepat(pat_list) ->
      print_tuple_pat pat_list
  | Crecordpat(l) ->
      print_string "{";
      print_list (fun (gl, pat) -> print_qualified_ident gl;
                                 print_string "=";
                           print_pattern (pri_e - 1) pat)
                 (fun () -> print_string ";") l;
      print_string "}"
  | Corpat(pat1, pat2) ->
      print_pattern pri_e pat1;
      print_string "|";
      print_pattern pri_e pat2
  | Caliaspat(pat, s) ->
      print_pattern pri_e pat;
      print_space ();
      print_string "as";
      print_space ();
      print_string s
  | Cwildpat -> print_string "_"
  end;
  if pri > pri_e then print_string ")";
  close_box ()

and print_tuple_pat pat_list =
  print_string "(";
  print_list (print_pattern 0) (fun () -> print_string ",") pat_list;
  print_string ")"

and print_match_pat_expr prio (pat, expr) =
  open_box 2;
  print_pattern 0 pat;
  print_space (); print_string "->"; print_space ();
  print prio expr;
  close_box ();
  print_space ();;

(* print a definition *)
let print_definition (name, e) =
  print_string "let ";
  print_let_pat_expr (Cvarpat(name), e)

(* print code *)
let print_code e = print 0 e

(* print types *)
let rec print_type typ =
  open_box 1;
  begin match typ with
    Darrow(is_node, typ1, typ2) ->
      print_type typ1;
      if is_node then print_string " => " else print_string " -> ";
      print_type typ2
  | Dproduct(ty_list) ->
      print_list print_type (fun _ -> print_string " *") ty_list
  | Dconstr(qual_ident, ty_list) ->
      if ty_list <> [] then
  begin
    print_string "(";
    print_list print_type (fun _ -> print_string ",") ty_list;
    print_string ")";
    print_space ()
  end;
      print_qualified_ident qual_ident
  | Dtypvar(i) -> print_type_name i
  | Dbase(b) -> print_base_type b
  | Dsignal(ty) -> print_type ty; print_space (); print_string "sig"
  end;
  close_box ()

and print_type_name n =
  print_string "'a";
  print_int n

and print_base_type b =
  match b with
    Dtyp_bool -> print_string "bool"
  | Dtyp_int -> print_string "int"
  | Dtyp_float -> print_string "float"
  | Dtyp_unit -> print_string "unit"
  | Dtyp_string -> print_string "string"
  | Dtyp_char -> print_string "char"

(* print variant *)
let print_variant (qualid, { arg = typ_list; res = typ }) =
  print_string " | ";
  print_qualified_ident qualid;
  match typ_list with
    [] -> (* arity = 0 *)
          ()
  | _ -> print_string " of ";
         print_list print_type (fun () -> print_string "*") typ_list

let print_record (qualid, is_mutable, { res = typ1 }) =
  if is_mutable then print_string "mutable ";
  print_qualified_ident qualid;
  print_string ":";
  print_type typ1;
  print_string ";"

let print_type_declaration s { d_type_desc = td; d_type_arity = l } =
  open_box 2;
  if l <> [] then
    begin
      print_string "(";
      print_list print_type_name (fun _ -> print_string ",") l;
      print_string ")";
      print_space ()
    end;
  print_string s;
  print_string " = ";
  begin match td with
    Dabstract_type -> ()
  | Dabbrev(ty) ->
      print_type ty
  | Dvariant_type variant_list ->
      List.iter print_variant variant_list
  | Drecord_type record_list ->
      print_string "{";
      print_list print_record (fun _ -> ()) record_list;
      print_string "}"
  end;
  print_newline ();
  close_box ()

let print_type_declarations l =
  let rec printrec l =
    match l with
      [] -> ()
    | [s, d] -> print_type_declaration s d
    | (s, d) :: l ->
  print_type_declaration s d;
  print_string "and ";
  printrec l in
  open_box 0;
  print_string "type ";
  printrec l;
  print_newline ();
  close_box ();;

(* the main function *)
set_max_boxes max_int ;;

let output_expr oc e =
  (* emit on channel oc *)
  set_formatter_out_channel oc;
  print 0 e;
  print_flush ()

let output_code oc c =
  (* emit on channel oc *)
  set_formatter_out_channel oc;
  print_code c

let output_definitions oc d_list =
  (* emit on channel oc *)
  set_formatter_out_channel oc;
  print_list print_definition print_newline d_list;
  print_flush ()

let output oc caml_code =
  set_formatter_out_channel oc;
  (* print type declarations *)
  let l = Misc.listoftable caml_code.c_types in
  if l <> [] then print_type_declarations l;
  (* print value definitions *)
  print_list print_definition print_newline caml_code.c_code;
  print_flush ()

