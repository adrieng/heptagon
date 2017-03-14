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


open Signature
open Modules
open Format
open Obc
open Misc
open Types
open Names
open Idents
open Pp_tools

let jname_of_name name =
  let b = Buffer.create (String.length name) in
  let rec convert c =
    match c with
      | 'A'..'Z' | 'a'..'z' | '0'..'9' | '_' ->
          Buffer.add_char b c
      | '\'' -> Buffer.add_string b "_prime"
      | _ ->
          Buffer.add_string b "lex";
          Buffer.add_string b (string_of_int (Char.code c));
          Buffer.add_string b "_" in

  String.iter convert name;
  Buffer.contents b

let print_name ff name =
  fprintf ff "%s" (jname_of_name name)

let print_shortname ff longname =
  print_name ff (shortname longname)

let rec java_type_default_value = function
  | Tid id when id = Initial.pint -> "int", "0"
  | Tid id when id = Initial.pfloat -> "float", "0.0"
  | Tid id when id = Initial.pbool -> "boolean", "false"
  | Tid t ->
      (match find_type t with
        | Tabstract -> assert false
        | Talias t -> java_type_default_value t
        | Tenum _ -> "int", "0" (* TODO java *)
        | Tstruct _ -> shortname t, "null" )
  | Tarray _ -> assert false (* TODO array *)
  | Tprod _ -> assert false (* TODO java *)
  | Tunit -> "void", "null"

let print_type ff ty =
  let jty,_ = java_type_default_value ty in
  print_name ff jty

let print_field ff (name,ty) =
  fprintf ff "%a %a;"
    print_type ty
    print_name name

let print_const_field ff (name,ty) =
  fprintf ff "%a@ %a"
    print_type ty
    print_name name

let print_assgt_field ff (name,_) =
  fprintf ff "this.%a = %a;"
    print_name name
    print_name name

(* assumes tn is already translated with jname_of_name *)
let print_struct_type ff tn fields =
  fprintf ff "@[<v>@[<v 2>public class %s {@ " tn;
  (* fields *)
  print_list print_field "" "" "" ff fields;
  (* constructor *)
  let sorted_fields =
    List.sort
      (fun (n1,_) (n2,_) -> String.compare n1 n2)
      fields in
  fprintf ff "@ @[<v 2>public %s(@[<hov>" tn;
  print_list print_const_field "" "," "" ff sorted_fields;
  fprintf ff "@]) {@ ";
  (* constructor assignments *)
  print_list print_assgt_field "" "" "" ff fields;
  (* constructor end *)
  fprintf ff "@]@ }";
  (* class end *)
  fprintf ff "@]@ }@]"


let rec print_tags ff n = function
  | []   -> ()
  | tg :: tgs' ->
      fprintf ff "@ public static final int %a = %d;"
        print_name ( shortname tg ) (* TODO java deal with modules *)
        n;
      print_tags ff (n+1) tgs'

(* assumes tn is already translated with jname_of_name *)
let print_enum_type ff tn tgs =
  fprintf ff "@[<v>@[<v 2>public class %s {" tn;
  print_tags ff 1 tgs;
  fprintf ff "@]@ }@]"

let rec print_type_to_file java_dir headers { t_name = tn; t_desc = td} =
  let tn = jname_of_name (shortname tn) in (* TODO java deal with modules *)
  match td with
    | Type_abs -> ()
    | Type_enum tgs ->
        let out_ch = open_out (java_dir ^ "/" ^ tn ^ ".java") in
        let ff = formatter_of_out_channel out_ch in
        (*Misc.print_header_info ff "/*" "*/"; *)
        List.iter (fprintf ff "%s") headers;
        (* fprintf ff "@[<v>package %s;@\n@\n" headers; *) (* TODO java deal with modules *)
        print_enum_type ff tn tgs;
        fprintf ff "@.";
        close_out out_ch
    | Type_struct fields ->
        let out_ch = open_out (java_dir ^ "/" ^ tn ^ ".java") in
        let ff = formatter_of_out_channel out_ch in
       (* Misc.print_header_info ff "/*" "*/"; *)(* TODO java deal with modules *)
        List.iter (fprintf ff "%s") headers;
        (* fprintf ff "@[<v>package %s;@\n@\n" headers; *)
        print_struct_type ff tn
                          (List.map (fun {f_name = n;f_type = t} -> (shortname n,t)) fields);
        (* TODO java deal with modules *)
        fprintf ff "@.";
        close_out out_ch
    | Type_alias t -> assert false (* TODO java *)

let print_types java_dir headers tps =
  List.iter (print_type_to_file java_dir headers) tps

(******************************)

type answer =
  | Sing of var_ident
  | Mult of var_ident list

let print_const ff c ts =
  match c.se_desc with
    | Sint i -> fprintf ff "%d" i
    | Sfloat f -> fprintf ff "%f" f
    | Sbool true -> fprintf ff "true"
    | Sbool false -> fprintf ff "false"
    | Sconstructor c ->
        let tg = shortname c in (* TODO java gérer les modules *)
        let s = (fst (List.find (fun (tn, tgs) -> List.exists (fun tg' -> tg = tg') tgs) ts))
                ^ "." ^ (jname_of_name tg) in
        fprintf ff "%s" s
    | _ -> assert false (* TODO java *)

let position a xs =
  let rec walk i = function
    | []       -> None
    | x :: xs' -> if x = a then Some i else walk (i + 1) xs'
  in walk 1 xs

let print_ident ff id =
  print_name ff (name id)

let print_var ff x avs single =
  match (position x avs) with
    | None -> print_ident ff x
    | Some n ->
        if single then print_ident ff (List.hd avs)
        else fprintf ff "step_ans.c_%d" n

let javaop_of_op = function
  | "="  -> "=="
  | "<>" -> "!="
  | "or" -> "||"
  | "&"  -> "&&"
  | "*." -> "*"
  | "/." -> "/"
  | "+." -> "+"
  | "-." -> "-"
  | op   -> op

let priority = function
  | "*" | "/" | "*." | "/."  -> 5
  | "+" | "-" | "+." | "-."  -> 4
  | "=" | "<>" | "<=" | "=>" -> 3
  | "&"                      -> 2
  | "|"                      -> 1
  | _                        -> 0

let rec print_lhs ff e avs single =
  match e.pat_desc with
    | Lvar x ->
        print_var ff x avs single
    | Lmem x -> print_ident ff x
    | Lfield(e, field) ->
        print_lhs ff e avs single;
        fprintf ff ".%s" (jname_of_name (shortname field))
    | Larray _ -> assert false (* TODO java array *)

let rec print_exp ff e p avs ts single =
  match e.e_desc with
    | Epattern l -> print_lhs ff l avs single
    | Econst c -> print_const ff c ts
    | Eop (op, es) -> print_op ff op es p avs ts single
    | Estruct (type_name,fields) ->
        let fields =
          List.sort
            (fun (ln1,_) (ln2,_) ->
               String.compare (shortname ln1) (shortname ln2))
            fields in
        let exps = List.map (fun (_,e) -> e) fields in
        fprintf ff "new %a(@[<hov>"
          print_shortname type_name;
        print_exps ff exps 0 avs ts single;
        fprintf ff "@])"
    | Earray _ -> assert false (* TODO array *)

and print_exps ff es p avs ts single =
  match es with
    | [] -> ()
    | [e] -> print_exp ff e p avs ts single
    | e :: es' ->
        print_exp ff e p avs ts single;
        fprintf ff ",@ ";
        print_exps ff es' p avs ts single

and print_op ff op es p avs ts single =
  match (shortname op), es with
    | (("+" | "-" | "*" | "/"
       |"+." | "-." | "*." | "/."
       | "=" | "<>" | "<" | "<="
       | ">" | ">=" | "&" | "or") as op_name, [e1;e2]) ->
        let p' = priority op_name in
        if p' < p then fprintf ff "(" else ();
        print_exp ff e1 p' avs ts single;
        fprintf ff " %s " (javaop_of_op op_name);
        print_exp ff e2 p' avs ts single;
        if p' < p then fprintf ff ")" else ()
    | "not", [e] ->
        fprintf ff "!";
        print_exp ff e 6 avs ts single;
    | "~-", [e] ->
        fprintf ff "-";
        print_exp ff e 6 avs ts single;
    | _ ->(*
        begin
          begin
            match op with
              | Name(op_name) ->
                  print_name ff op_name;
              | Modname({ qual = mod_name; id = op_name }) ->
                  fprintf ff "%a.%a"
                    print_name (String.uncapitalize mod_name)
                    print_name op_name
          end;
          fprintf ff "@[(";
          print_exps ff es 0 avs ts single;
          fprintf ff ")@]"
        end *)
        assert false (* TODO java *)

let rec print_proj ff xs ao avs single =
  let rec walk ind = function
    | [] -> ()
    | x :: xs' ->
        print_lhs ff x avs single;
        fprintf ff " = %s.c_%d;@ " ao ind;
        walk (ind + 1) xs'
  in walk 1 xs


let bool_case = function
  | []                -> assert false
  | ("true", _) :: _
  | ("false", _) :: _ -> true
  | _                 -> false

let obj_ref_to_string = function
  | Oobj o -> o
  | Oarray (o,p) -> o (* TODO java array *)

let rec print_act ff a objs avs ts single =
  match a with
    | Aassgn (x, e) ->
        fprintf ff "@[";
        print_asgn ff x e avs ts single;
        fprintf ff ";@]"
    | Acall (xs,oref,Mstep,es) ->
        let o = obj_ref_to_string oref in
        (match xs with
           | [x] ->
               print_lhs ff x avs single;
               fprintf ff " = %s.step(" o;
               fprintf ff "@[";
               print_exps ff es 0 avs ts single;
               fprintf ff "@]";
               fprintf ff ");@ "
           | xs ->
               let cn = (List.find (fun od -> od.o_name = o) objs).o_class in
               let at = (jname_of_name (shortname cn)) ^ "Answer" in
               let ao = o ^ "_ans" in
               fprintf ff "%s %s = new %s();@ " at ao at;
               fprintf ff "%s = %s.step(" ao o;
               fprintf ff "@[";
               print_exps ff es 0 avs ts single;
               fprintf ff "@]";
               fprintf ff ");@ ";
               print_proj ff xs ao avs single)
    | Acase (e, grds) ->
        let grds =
          List.map
            (fun (ln,act) -> (shortname ln),act) grds in
        if bool_case grds
        then print_if ff e grds objs avs ts single
        else (fprintf ff "@[<v>@[<v 2>switch (%a) {@ "
                (fun ff e -> print_exp ff e 0 avs ts single) e;
              print_grds ff grds objs avs ts single;
              fprintf ff "@]@ }@]");
    | Acall (_,oref,Mreset,_) ->
        let o = obj_ref_to_string oref in
        fprintf ff "%s.reset();" o
    | Afor _ -> assert false (* TODO java array *)


and print_grds ff grds objs avs ts single =
  match grds with
    | [] -> ()
    | (tg, b) :: grds' ->
        (* retrieve class name *)
        let cn = (fst
                    (List.find
                       (fun (tn, tgs) ->
                          List.exists (fun tg' -> tg = tg') tgs)
                       ts)) in
        fprintf ff "@[<v 2>case %a.%a:@ "
          print_name cn
          print_name tg;
        print_block ff b objs avs ts single;
        fprintf ff "@ break;@ @]@ ";
        print_grds ff grds' objs avs ts single

and print_if ff e grds objs avs ts single =
  match grds with
    | [("true", a)] ->
        fprintf ff "@[<v>@[<v 2>if (%a) {@ "
          (fun ff e -> print_exp ff e 0 avs ts single) e;
        print_block ff a objs avs ts single;
        fprintf ff "@]@ }@]"
    | [("false", a)] ->
        fprintf ff "@[<v>@[<v 2>if (!%a) {@ "
          (fun ff e -> print_exp ff e 6 avs ts single) e;
        print_block ff a objs avs ts single;
        fprintf ff "@]@ }@]"
    | [("true", a1); ("false", a2)] ->
        fprintf ff "@[<v>@[<v 2>if (%a) {@ "
          (fun ff e -> print_exp ff e 0 avs ts single) e;
        print_block ff a1 objs avs ts single;
        fprintf ff "@]@ @[<v 2>} else {@ ";
        print_block ff a2 objs avs ts single;
        fprintf ff "@]@ }@]"
    | [("false", a2); ("true", a1)] ->
        fprintf ff "@[<v>@[<v 2>if (%a) {@ "
          (fun ff e -> print_exp ff e 0 avs ts single) e;
        print_block ff a1 objs avs ts single;
        fprintf ff "@]@ @[<v 2>} else {@ ";
        print_block ff a2 objs avs ts single;
        fprintf ff "@]@ }@]"
    | _ -> assert false

and print_asgn ff x e avs ts single =
  fprintf ff "@[";
  print_lhs ff x avs single;
  fprintf ff " = ";
  print_exp ff e 0 avs ts single;
  fprintf ff "@]"

and print_block ff b objs avs ts single  = () (* TODO urgent java *)

let print_vd ff vd =
  let jty,jdv = java_type_default_value vd.v_type in
  fprintf ff "@[<v>";
  print_name ff jty;
  fprintf ff " %s = %s;"
    (jname_of_name (name vd.v_ident))
    jdv;
  fprintf ff "@]"

let print_obj ff od =
  fprintf ff "@[<v>";
  fprintf ff "%a %a = new %a();"
    print_shortname od.o_class
    print_name od.o_name
    print_shortname od.o_class;
  fprintf ff "@]"

let rec print_objs ff ods =
  match ods with
    | [] -> ()
    | od :: ods' ->
        print_obj ff od;
        fprintf ff "@ ";
        print_objs ff ods'

let print_comps ff fds=
  let rec walk n = function
    | [] -> ()
    | fd :: fds' ->
        fprintf ff "@ ";
        fprintf ff "public ";
        print_type ff fd.v_type;
        fprintf ff " c_%s;" (string_of_int n);
        walk (n + 1) fds'
  in walk 1 fds

let print_ans_struct ff name fields =
  fprintf ff "@[<v>@[<v 2>public class %s {" name;
  print_comps ff fields;
  fprintf ff "@]@ }@]@ "

let print_vd' ff vd =
  fprintf ff "@[";
  print_type ff vd.v_type;
  fprintf ff "@ %s" (jname_of_name (name vd.v_ident));
  fprintf ff "@]"

let rec print_in ff = function
  | [] -> ()
  | [vd] -> print_vd' ff vd
  | vd :: vds' ->
      print_vd' ff vd;
      fprintf ff ",@ ";
      print_in ff vds'

let rec print_mem ff = function
  | [] -> ()
  | vd :: m' ->
      print_vd ff vd;
      fprintf ff "@ ";
      print_mem ff m'

let print_loc ff vds = print_mem ff vds

let print_step ff n s objs ts single =
  let n = jname_of_name n in
  fprintf ff "@[<v>@ @[<v 2>public ";
  if single then print_type ff (List.hd s.m_outputs).v_type
  else fprintf ff "%s" (n ^ "Answer");
  fprintf ff " step(@[";
  print_in ff s.m_inputs;
  fprintf ff "@]) {@ ";
  let loc = if single then (List.hd s.m_outputs) :: s.m_body.b_locals else s.m_body.b_locals in
  if loc = [] then () else (print_loc ff loc; fprintf ff "@ ");
  if single then fprintf ff "@ "
  else fprintf ff "%sAnswer step_ans = new %sAnswer();@ @ " n n;
  print_act ff s.bd objs
    (List.map (fun vd -> vd.v_ident) s.out) ts single;
  fprintf ff "@ @ return ";
  if single
  then fprintf ff "%s" (jname_of_name (Idents.name (List.hd s.out).v_ident))
  else fprintf ff "step_ans";
  fprintf ff ";@]@ }@ @]"

let print_reset ff r ts =
  fprintf ff "@[<v>@ @[<v 2>public void reset() {@ ";
  print_act ff r [] [] ts false;
  fprintf ff "@]@ }@ @]"

let print_class ff headers ts single opened_mod cl =
  let clid = jname_of_name cl.cl_id in
  List.iter (fprintf ff "%s") headers;
  (*   fprintf ff "@[<v>package %s;@\n@\n" headers; *)
  (* import opened modules *)
  List.iter
    (fun m ->
       fprintf ff "import %s.*;@\n" (String.uncapitalize_ascii m))
    opened_mod;

  fprintf ff "@\n@[<v 2>public class %s {@ " clid;
  if cl.mem = [] then ()
  else fprintf ff "@[<v>@ "; print_mem ff cl.mem; fprintf ff "@]";
  if cl.objs = [] then ()
  else fprintf ff "@[<v>@ "; print_objs ff cl.objs; fprintf ff "@]";
  print_reset ff cl.reset ts;
  print_step ff clid cl.step cl.objs ts single;
  fprintf ff "@]@ }@]"

let print_class_and_answer_to_file java_dir headers ts opened_mod cl =
  let clid = jname_of_name cl.cl_id in
  let print_class_to_file single =
    let out_ch = open_out (java_dir ^ "/" ^ clid ^ ".java") in
    let ff = formatter_of_out_channel out_ch in
    Misc.print_header_info ff "/*" "*/";
    print_class ff headers ts single opened_mod cl;
    fprintf ff "@.";
    close_out out_ch
  in
  match cl.step.out with
    | [_] -> print_class_to_file true
    | _ ->
        let out_ch = open_out (java_dir ^ "/" ^ clid ^ "Answer.java") in
        let ff = formatter_of_out_channel out_ch in
        Misc.print_header_info ff "/*" "*/";
        List.iter (fprintf ff "%s") headers;
        (*         fprintf ff "@[<v>package %s;@\n@\n" headers; *)
        List.iter
          (fun m ->
             fprintf ff "import %s.*;@\n" (String.uncapitalize_ascii m))
          opened_mod;
        print_ans_struct ff (clid ^ "Answer") cl.step.out;
        fprintf ff "@.";
        close_out out_ch;
        print_class_to_file false

let print_classes java_dir headers ts opened_mod cls =
  List.iter
    (print_class_and_answer_to_file java_dir headers ts opened_mod)
    cls

(******************************)
let print java_dir p =
  let headers =
    List.map snd
      (List.filter
         (fun (tag,_) -> tag = "java")
         p.o_pragmas) in
  print_types java_dir headers p.o_types;
  o_types := p.o_types;
  print_classes
    java_dir headers
    (List.flatten
       (List.map
          (function
             | { t_desc = Type_abs }                   -> []
             | { t_name = tn; t_desc = Type_enum tgs } -> [tn, tgs]
             | { t_name = tn; t_desc = Type_struct fields } ->
                 [tn, (List.map fst fields)])
          p.o_types))
    p.o_opened
    p.o_defs

(******************************)
