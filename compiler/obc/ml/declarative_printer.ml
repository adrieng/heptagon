(**************************************************************************)
(*                                                                        *)
(*  Lucid Synchrone                                                       *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* $Id: declarative_printer.ml,v 1.13 2007-01-11 07:35:53 pouzet Exp $ *)

open Misc
open Names
open Declarative
open Modules
open Format

(* generic printing of a list *)
let print_list print l =
  let rec printrec l =
    match l with
      [] -> ()
    | [x] ->
  print x
    | x::l ->
  print x;
  print_space ();
  printrec l in
  printrec l

(* local name *)
let print_name i =
  print_string "/";print_int i

(* global names *)
let print_qualified_ident { qual = q; id = id } =
  if (q = pervasives_module) or (q = compiled_module_name ())
     or (q = "")
  then print_string id
  else
    begin
      print_string q;
      print_string ".";
      print_string id
    end

(* print types *)
let rec print_type typ =
  open_box 1;
  begin match typ with
    Darrow(is_node, typ1, typ2) ->
      print_string "(";
      if is_node then print_string "=>" else print_string "->";
      print_space ();
      print_list print_type [typ1;typ2];
      print_string ")"
  | Dproduct(ty_list) ->
      print_string "(";
      print_string "*";
      print_space ();
      print_list print_type ty_list;
      print_string ")"
  | Dconstr(qual_ident, ty_list) ->
      if ty_list <> [] then print_string "(";
      print_qualified_ident qual_ident;
      if ty_list <> [] then
  begin print_space ();
    print_list print_type ty_list;
    print_string ")"
  end
  | Dsignal(ty) -> print_type ty; print_space (); print_string "sig"
  | Dtypvar(i) -> print_int i
  | Dbase(b) -> print_base_type b
  end;
  close_box ()

and print_base_type b =
  match b with
    Dtyp_bool -> print_string "bool"
  | Dtyp_int -> print_string "int"
  | Dtyp_float -> print_string "float"
  | Dtyp_unit -> print_string "unit"
  | Dtyp_string -> print_string "string"
  | Dtyp_char -> print_string "char"

let print_typs (Dtypforall(l, typ)) =
  match l with
    [] -> (* we do not print the quantifier when there is no type variable *)
      print_type typ
  | l ->
      open_box 1;
      print_string "(forall";
      print_space ();
      print_list print_name l;
      print_space ();
      print_type typ;
      print_string ")";
      close_box ()

(* print clocks *)
let rec print_clock clk =
  match clk with
  | Dfalse -> print_string "false"
  | Dtrue -> print_string "true"
  | Dclockvar(i) -> print_name i
  | Don(b, clk, c) ->
      print_string "(";
      if b then print_string "on" else print_string "onot";
      print_space ();
      print_clock clk;
      print_space ();
      print_carrier c;
      print_string ")"
and print_carrier c =
  match c with
    Dcfalse -> print_string "false"
  | Dctrue -> print_string "true"
  | Dcvar(i) -> print_name i
  | Dcglobal(qual_ident, res, clk) ->
      print_qualified_ident qual_ident;
      print_string "(";
      (match res with
  None -> ()
      | Some(n) -> print_space ();print_name n;print_space ());
      print_clock clk;
      print_string ")"

(* immediate values *)
let print_immediate i =
  match i with
    Dbool(b) -> print_string (if b then "true" else "false")
  | Dint(i) -> print_int i
  | Dfloat(f) -> print_float f
  | Dchar(c) -> print_char c
  | Dstring(s) -> print_string s
  | Dvoid -> print_string "()"

(* print patterns *)
let atom_pat pat =
  match pat with
    Dconstantpat _ | Dvarpat _ | Dwildpat -> true
  | _ -> false

let rec print_pat pat =
  open_box 1;
  if not (atom_pat pat) then print_string "(";
  begin match pat with
    Dwildpat -> print_string "_"
  | Dconstantpat(i) -> print_immediate i
  | Dvarpat(i) -> print_name i
  | Dconstructpat(qual_ident, pat_list) ->
      print_string "constr";
      print_space ();
      print_qualified_ident qual_ident;
      if pat_list <> [] then print_space ();
      print_list print_pat pat_list
  | Dtuplepat(pat_list) ->
      print_string ",";
      print_space ();
      print_list print_pat pat_list
  | Drecordpat(l) ->
      print_string "record";
      print_list
  (fun (qual_ident, pat) ->
    open_box 1;
    print_string "(";
    print_qualified_ident qual_ident;
    print_space ();
    print_pat pat;
    print_string ")";
    close_box ()) l
  | Dorpat(pat1, pat2) ->
      print_string "orpat";
      print_space ();
      print_list print_pat [pat1;pat2]
  | Daliaspat(pat, i) ->
      print_string "as";
      print_space ();
      print_pat pat;
      print_space ();
      print_int i
  end;
  if not (atom_pat pat) then print_string ")";
  close_box ()

(* print statepat *)
let print_statepat (s, l) =
  match l with
    [] -> print_string s
  | l -> print_string "(";
         print_string s;
         print_space ();
         print_list print_pat l;
         print_string ")"

(* print expressions *)
let atom e =
  match e.d_desc with
    Dconstant _ -> true
  | _ -> false

(* print variables *)
let print_var v =
  match v with
    Dlocal(n) ->
      print_string "local";
      print_space ();
      print_name n
  | Dglobal(qual_ident) ->
      print_string "global";
      print_space ();
      print_qualified_ident qual_ident

let rec print e =
  open_box 1;
  if not (atom e) then print_string "(";
  begin match e.d_desc with
    Dconstant(i) -> print_immediate i
  | Dvar(v, subst) ->
      print_var v;
      print_subst subst
  | Dlast(i) ->
      print_string "last";
      print_space ();
      print_name i
  | Dpre(opt_default, e) ->
      print_string "pre";
      print_space ();
      begin match opt_default with
  None -> print e
      | Some(default) ->
    print default; print_space (); print e
      end
  | Dinit(ck, None) ->
      print_string "init";
      print_space ();
      print_clock ck
  | Dinit(ck, Some(n)) ->
      print_string "init";
      print_space ();
      print_clock ck;
      print_space ();
      print_name n
  | Difthenelse(e0,e1,e2) ->
      print_string "if";
      print_space ();
      print e0;
      print_space ();
      print e1;
      print_space ();
      print e2
  | Dtuple(l) ->
      print_string ",";
      print_space ();
      print_list print l
  | Dconstruct(qual_ident,l) ->
      print_string "constr";
      print_space ();
      print_qualified_ident qual_ident;
      if l <> [] then print_space ();
      print_list print l
  | Dprim(qual_ident, l) ->
      print_string "(";
      print_qualified_ident qual_ident;
      print_space ();
      print_list print l;
      print_string ")"
  | Drecord(l) ->
      print_string "record";
      print_space ();
      print_list (fun (qual_ident, e) ->
  open_box 1;
  print_string "(";
  print_qualified_ident qual_ident;
  print_space ();
  print e;
  print_string ")";
  close_box ()) l
  | Drecord_access(e,qual_ident) ->
      print_string "access";
      print_space ();
      print e;
      print_space ();
      print_qualified_ident qual_ident
  | Dfun(is_state, params, args, block, e) ->
      print_string ("fun" ^ (if is_state then "(s)" else "(c)"));
      print_space ();
      print_params params;
      print_space ();
      print_list print_pat args;
      print_space ();
      print_block block;
      print_space ();
      print_string "return ";
      print e
  | Dapply(is_state, f, e_list) ->
      print_string ("apply" ^ (if is_state then "(s)" else "(c)"));
      print_space ();
      print f;
      print_space ();
      print_list print e_list
  | Dlet(block, e) ->
      print_string "let";
      print_space ();
      print_block block;
      print_space ();
      print e
  | Deseq(e1, e2) ->
      print_string "seq";
      print_space ();
      print e1;
      print_space ();
      print e2
  | Dtest(e1) ->
      print_string "test";
      print_space ();
      print e1
  | Dwhen(e1) ->
      print_string "when";
      print_space ();
      print e1
  | Dclock(ck) ->
      print_string "clock";
      print_space ();
      print_clock ck
  end;
  if not (atom e) then print_string ")";
  close_box()

and print_block b =
  (* print variable definitions *)
  let print_env env =
    open_box 1;
    print_string "(env";
    print_space ();
    Hashtbl.iter (fun i ident -> print_ident ident;print_space ()) env;
    print_string ")";
    close_box () in
  (* main function *)
  open_box 1;
  print_string "(";
  (* environment *)
  print_env b.b_env;
  print_space ();
  (* equations *)
  print_equation b.b_equations;
  print_space ();
  (* write variables *)
  print_string "(write";
  print_space ();
  print_list print_name b.b_write;
  print_string ")";
  print_string ")";
  close_box ()

(* print ident declarations *)
(* e.g, "(kind x/412 (int) (cl) (write) (last) (signal) (= 412))" *)
and print_ident id =
  let print_kind () =
    match id.id_kind with
      Kinit -> print_string "init"
    | Kclock -> print_string "clock"
    | Kmemo -> print_string "memo"
    | Kstatic -> print_string "static"
    | Klast -> print_string "last"
    | Kreset -> print_string "reset"
    | Kvalue -> print_string "value"
    | Kinput -> print_string "input"
    | Kshared -> print_string "shared" in
  let print_name () =
    begin match id.id_original with
      None -> ()
    | Some(s) -> print_string s
    end;
    print_name id.id_name in
  let print_typs () =
    print_string "(";
    print_typs id.id_typ;
    print_string ")" in
  let print_write () =
    if id.id_write then
      begin print_space (); print_string "(write)" end in
  let print_last () =
    if id.id_last then
      begin print_space (); print_string "(last)" end in
  let print_signal () =
    if id.id_signal then
      begin print_space (); print_string "(signal)" end in
  let print_expr () =
    match id.id_value with
      None -> ()
    | Some(e) ->
  print_space ();print_string "(= "; print e; print_string ")" in
  (* main function *)
  open_box 1;
  print_string "(";
  print_kind ();
  print_space ();
  print_name ();
  print_space ();
  print_typs ();
  print_space ();
  print_write ();
  print_last ();
  print_signal ();
  print_expr ();
  print_string ")";
  close_box ()

(* prints a sequence of sets of parallel equations *)
and print_equation eq =
  open_box 1;
  print_string "(";
  begin match eq with
    Dequation(pat, e) ->
      print_string "let";
      print_space ();
      print_pat pat;
      print_space ();
      print e;
      print_space ();
      print_clock e.d_guard
  | Dlasteq(n, e) ->
      print_string "last";
      print_space ();
      print_name n;
      print_space ();
      print e;
      print_space ();
      print_clock e.d_guard
  | Demit(pat, e) ->
      print_string "emit";
      print_space ();
      print_pat pat;
      print_space ();
      print e;
      print_space ();
      print_clock e.d_guard
  | Dstatic(pat, e) ->
      print_string "static";
      print_space ();
      print_pat pat;
      print_space ();
      print e;
      print_space ();
      print_clock e.d_guard
  | Dnext(n, e) ->
      print_string "next";
      print_space ();
      print_name n;
      print_space ();
      print e;
      print_space ();
      print_clock e.d_guard
  | Dget(pat, v) ->
      print_string "get";
      print_space ();
      print_pat pat;
      print_space ();
      print_var v
  | Dwheneq(eq, clk) ->
      print_string "when";
      print_space ();
      print_clock clk;
      print_space ();
      print_equation eq
  | Dmerge(is_static, e, pat_block_list) ->
      print_string "merge";
      print_space ();
      if is_static then print_string "static"
      else print_clock e.d_guard;
      print_space ();
      print e;
      print_space ();
      print_list (fun (pat, block) ->
                  open_box 1;
                  print_string "(";
                        print_pat pat;
                  print_space ();
                  print_block block;
                  print_string ")";
                        close_box ()) pat_block_list
  | Dpresent(ck, scondpat_block_list, block) ->
      print_string "present";
      print_space ();
      print_clock ck;
      print_space ();
      print_list (fun (scondpat, block) ->
                  open_box 1;
                  print_string "(";
                        print_spat scondpat;
                  print_space ();
                  print_block block;
                  print_string ")";
                        close_box ()) scondpat_block_list;
      print_space ();
      print_block block
  | Dreset(eq, e) ->
      print_string "reset";
      print_space ();
      print_equation eq;
      print_space ();
      print e
  | Dautomaton(ck, handlers) ->
      print_string "automaton";
      print_space ();
      print_clock ck;
      print_space ();
      print_list print_handler handlers
  | Dpar(eq_list) ->
      print_string "par";
      print_space ();
      print_list print_equation eq_list
  | Dseq(eq_list) ->
      print_string "seq";
      print_space ();
      print_list print_equation eq_list
  | Dblock(b) ->
      print_string "block";
      print_space ();
      print_block b
  end;
  print_string ")";
  close_box ()

(* print the handlers of an automaton *)
and print_handler (statepat, b_weak, b_strong, weak_escape, strong_escape) =
  open_box 1;
  print_string "(state";
  print_space ();
  print_statepat statepat;
  print_space ();
  print_block b_weak;
  print_space ();
  print_block b_strong;
  print_space ();
  print_string "(weak ";
  print_escape weak_escape;
  print_string ")";
  print_space ();
  print_string "(strong ";
  print_escape weak_escape;
  print_string ")";
  print_string ")";
  close_box ()

and print_escape escape_list =
  print_list
    (fun (spat, b, is_continue, state) ->
      print_string "(";
      if is_continue then print_string "continue " else print_string "then ";
      print_spat spat;
      print_space ();
      print_block b;
      print_space ();
      print_state state;
      print_string ")")
    escape_list;
  close_box ()


(* print type and clock instance *)
and print_subst { s_typ = st; s_clock = scl; s_carrier = sc } =
  match st, scl, sc with
    [],[],[] -> ()
  | l1,l2,l3 ->
      print_string "[";
      print_list print_type l1;
      print_string "]";
      print_space ();
      print_string "[";
      print_list print_clock l2;
      print_string "]";
      print_space ();
      print_string "[";
      print_list print_carrier l3;
      print_string "]";

and print_params { s_typ = pt; s_clock = pcl; s_carrier = pc } =
  match pt, pcl, pc with
    [],[],[] -> ()
  | l1,l2,l3 ->
      print_string "[";
      print_list print_name l1;
      print_string "]";
      print_space ();
      print_string "[";
      print_list print_name l2;
      print_string "]";
      print_space ();
      print_string "[";
      print_list print_name l3;
      print_string "]"

and print_state (s, l) =
  match l with
    [] -> print_string s
  | l -> print_string "(";
         print_string s;
         print_space ();
         print_list print l;
   print_string ")"

and atom_spat spat =
  match spat with
    Dexppat _ | Dcondpat _ -> true
  | _ -> false

and print_spat spat =
  open_box 1;
  if not (atom_spat spat) then print_string "(";
  begin match spat with
    Dandpat(spat1, spat2) ->
      print_string "& ";
      print_spat spat1;
      print_space ();
      print_spat spat2
  | Dexppat(e) ->
      print e
  | Dcondpat(e, pat) ->
      print_string "is ";
      print e;
      print_space ();
      print_pat pat
  end;
  if not (atom_spat spat) then print_string ")";
  close_box ()

(* the main entry for printing definitions *)
let print_definition (name, e) =
  open_box 2;
  print_string "(def ";
  if is_an_infix_or_prefix_operator name
  then begin print_string "( "; print_string name; print_string " )" end
  else print_string name;
  print_space ();
  print e;
  print_string ")";
  print_newline ();
  close_box ()

(* print types *)
let print_variant (qualid, { arg = typ_list; res = typ }) =
  print_string "(";
  print_qualified_ident qualid;
  print_string "(";
  print_list print_type typ_list;
  print_string ")";
  print_space ();
  print_type typ;
  print_string ")"

let print_record (qualid, is_mutable, { arg = typ1; res = typ2 }) =
  print_string "(";
  if is_mutable then print_string "true" else print_string "false";
  print_space ();
  print_qualified_ident qualid;
  print_space ();
  print_type typ1;
  print_space ();
  print_type typ2;
  print_string ")"

let print_type_declaration s { d_type_desc = td; d_type_arity = arity } =
  open_box 2;
  print_string "(type[";
  print_list print_name arity;
  print_string "]";
  print_space ();
  print_string s;
  print_space ();
  begin match td with
    Dabstract_type -> ()
  | Dabbrev(ty) ->
      print_type ty
  | Dvariant_type variant_list ->
      List.iter print_variant variant_list
  | Drecord_type record_list ->
      List.iter print_record record_list
  end;
  print_string ")";
  print_newline ();
  close_box ();;

(* the main functions *)
set_max_boxes max_int ;;

let output_equations oc eqs =
  set_formatter_out_channel oc;
  List.iter print_equation eqs

let output oc declarative_code =
  set_formatter_out_channel oc;
  (* print type declarations *)
  Hashtbl.iter print_type_declaration declarative_code.d_types;
  (* print value definitions *)
  List.iter print_definition declarative_code.d_code;
  print_flush ()

