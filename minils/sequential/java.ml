(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* $Id$ *)

open Global
open Modules
open Format
open Obc
open Misc
open Names
open Ident

let actual_type ty =
  match ty with
    | Tid(tn) when (shortname tn) = "float" -> Tfloat
    | Tid(tn) when (shortname tn) = "int" -> Tint
    | _ -> ty

(******************************)
let rec print_list ff print sep l =
  match l with
    | [] -> ()
    | [x] -> print ff x
    | x :: l ->
        print ff x;
        fprintf ff "%s@ " sep;
        print_list ff print sep l

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

let o_types : type_dec list ref = ref []

let java_type_default_value = function
  | Tint -> "int", "0"
  | Tfloat -> "float", "0.0"
  | Tid (Name("bool"))
  | Tid (Modname({ id = "bool" })) ->
      "boolean", "false"
  | Tid t when ((shortname t) = "int") -> "int", "0"
  | Tid t when ((shortname t) = "float") -> "float", "0.0"
  | Tid t ->
      begin try
        let { info = ty_desc } = find_type (t) in
	      begin match ty_desc with
	        | Tenum _ ->
	            "int", "0"
	        | _ ->
	            let t = shortname t in
	            if t = "bool"
	            then ("boolean", "false")
	            else (t, "null")
	      end
      with Not_found ->
	      begin try
	        let { t_desc = tdesc } =
	          List.find (fun {t_name = tn} -> tn = (shortname t)) !o_types in
	        begin match tdesc with
	          | Type_enum _ ->
	              "int", "0"
	          | _ ->
	              let t = shortname t in
	              if t = "bool"
	              then ("boolean", "false")
	              else (t, "null")
	        end
	      with Not_found ->
	        let t = shortname t in
	        if t = "bool"
	        then ("boolean", "false")
	        else (t, "null")
	      end
      end

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
  print_list ff print_field "" fields;
  (* constructor *)
  let sorted_fields =
    List.sort
      (fun (n1,_) (n2,_) -> String.compare n1 n2)
      fields in
  fprintf ff "@ @[<v 2>public %s(@[<hov>" tn;
  print_list ff print_const_field "," sorted_fields;
  fprintf ff "@]) {@ ";
  (* constructor assignments *)
  print_list ff print_assgt_field "" fields;
  (* constructor end *)
  fprintf ff "@]@ }";
  (* class end *)
  fprintf ff "@]@ }@]"


let rec print_tags ff n = function
  | []   -> ()
  | tg :: tgs' ->
      fprintf ff "@ public static final int %a = %d;"
	      print_name tg
	      n;
      print_tags ff (n+1) tgs'

(* assumes tn is already translated with jname_of_name *)
let print_enum_type ff tn tgs =
  fprintf ff "@[<v>@[<v 2>public class %s {" tn;
  print_tags ff 1 tgs;
  fprintf ff "@]@ }@]"

let print_type_to_file java_dir headers { t_name = tn; t_desc = td} =
  let tn = jname_of_name tn in
  match td with
    | Type_abs -> ()
    | Type_enum tgs ->
	      let out_ch = open_out (java_dir ^ "/" ^ tn ^ ".java") in
	      let ff = formatter_of_out_channel out_ch in
	      Misc.print_header_info ff "/*" "*/";
	      List.iter (fprintf ff "%s") headers;
	      (* fprintf ff "@[<v>package %s;@\n@\n" headers; *)
	      print_enum_type ff tn tgs;
	      fprintf ff "@.";
	      close_out out_ch
    | Type_struct fields ->
	      let out_ch = open_out (java_dir ^ "/" ^ tn ^ ".java") in
	      let ff = formatter_of_out_channel out_ch in
	      Misc.print_header_info ff "/*" "*/";
	      List.iter (fprintf ff "%s") headers;
	      (* fprintf ff "@[<v>package %s;@\n@\n" headers; *)
	      print_struct_type ff tn fields;
	      fprintf ff "@.";
	      close_out out_ch

let print_types java_dir headers tps =
  List.iter (print_type_to_file java_dir headers) tps

(******************************)

type answer =
  | Sing of var_name
  | Mult of var_name list

let print_const ff c ts =
  match c with
    | Cint i -> fprintf ff "%d" i
    | Cfloat f -> fprintf ff "%f" f
    | Cconstr t ->
        let s =
          match t with
	          | Name("true")
	          | Modname({id = "true"}) -> "true"
	          | Name("false")
	          | Modname({id = "false"}) -> "false"
	          | Name(tg)
	          | Modname({id = tg}) ->
	              (fst
                   (List.find
                      (fun (tn, tgs) ->
		                     List.exists (fun tg' -> tg = tg') tgs)
                      ts))
	              ^ "." ^ (jname_of_name tg)
        in
	      fprintf ff "%s" s

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
    match e with
      | Var x ->
          print_var ff x avs single
      | Mem x -> print_ident ff x
      | Field(e, field) ->
          print_lhs ff e avs single;
          fprintf ff ".%s" (jname_of_name (shortname field))

let rec print_exp ff e p avs ts single =
  match e with
    | Lhs l -> print_lhs ff l avs single
    | Const c -> print_const ff c ts
    | Op (op, es) -> print_op ff op es p avs ts single
    | Struct(type_name,fields) ->
        let fields =
	        List.sort
	          (fun (ln1,_) (ln2,_) -> String.compare (shortname ln1) (shortname ln2))
	          fields in
        let exps = List.map (fun (_,e) -> e) fields in
        fprintf ff "new %a(@[<hov>"
	        print_shortname type_name;
        print_exps ff exps 0 avs ts single;
        fprintf ff "@])"

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
    | _ ->
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
        end

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

let rec print_act ff a objs avs ts single =
  match a with
    | Assgn (x, e) ->
	      fprintf ff "@[";
	      print_asgn ff x e avs ts single;
	      fprintf ff ";@]"
    | Step_ap (xs, o, es) ->
	      (match xs with
	         | [x] ->
	             print_lhs ff x avs single;
	             fprintf ff " = %s.step(" o;
	             fprintf ff "@[";
               print_exps ff es 0 avs ts single;
               fprintf ff "@]";
	             fprintf ff ");@ "
	         | xs ->
	             let cn = (List.find (fun od -> od.obj = o) objs).cls in
	             let at = (jname_of_name (shortname cn)) ^ "Answer" in
	             let ao = o ^ "_ans" in
	             fprintf ff "%s %s = new %s();@ " at ao at;
	             fprintf ff "%s = %s.step(" ao o;
	             fprintf ff "@[";
               print_exps ff es 0 avs ts single;
               fprintf ff "@]";
	             fprintf ff ");@ ";
	             print_proj ff xs ao avs single)
    | Comp (a1, a2) ->
	      print_act ff a1 objs avs ts single;
	      (match a2 with
	         | Nothing -> ()
	         | _ -> fprintf ff "@ ");
	      print_act ff a2 objs avs ts single
    | Case (e, grds) ->
	      let grds =
	        List.map
	          (fun (ln,act) -> (shortname ln),act) grds in
	      if bool_case grds
	      then print_if ff e grds objs avs ts single
	      else (fprintf ff "@[<v>@[<v 2>switch (%a) {@ "
		            (fun ff e -> print_exp ff e 0 avs ts single) e;
	            print_grds ff grds objs avs ts single;
	            fprintf ff "@]@ }@]");
    | Reinit o -> fprintf ff "%s.reset();" o
    | Nothing -> ()

and print_grds ff grds objs avs ts single =
  match grds with
    | [] -> ()
    | [(tg, act)] ->
	      (* retrieve class name *)
	      let cn = (fst
		                (List.find
		                   (fun (tn, tgs) ->
			                    List.exists (fun tg' -> tg = tg') tgs)
		                   ts)) in
	      fprintf ff "@[<v 2>case %a.%a:@ "
	        print_name cn
	        print_name tg;
	      print_act ff act objs avs ts single;
	      fprintf ff "@ break;@]";	
    | (tg, act) :: grds' ->
	      (* retrieve class name *)
	      let cn = (fst
		                (List.find
		                   (fun (tn, tgs) ->
			                    List.exists (fun tg' -> tg = tg') tgs)
		                   ts)) in
	      fprintf ff "@[<v 2>case %a.%a:@ "
	        print_name cn
	        print_name tg;
	      print_act ff act objs avs ts single;
	      fprintf ff "@ break;@ @]@ ";
	      print_grds ff grds' objs avs ts single

and print_if ff e grds objs avs ts single =
  match grds with
    | [("true", a)] ->
	      fprintf ff "@[<v>@[<v 2>if (%a) {@ "
	        (fun ff e -> print_exp ff e 0 avs ts single) e;
	      print_act ff a objs avs ts single;
	      fprintf ff "@]@ }@]"
    | [("false", a)] ->
	      fprintf ff "@[<v>@[<v 2>if (!%a) {@ "
	        (fun ff e -> print_exp ff e 6 avs ts single) e;
	      print_act ff a objs avs ts single;
	      fprintf ff "@]@ }@]"
    | [("true", a1); ("false", a2)] ->
	      fprintf ff "@[<v>@[<v 2>if (%a) {@ "
	        (fun ff e -> print_exp ff e 0 avs ts single) e;
	      print_act ff a1 objs avs ts single;
	      fprintf ff "@]@ @[<v 2>} else {@ ";
	      print_act ff a2 objs avs ts single;
	      fprintf ff "@]@ }@]"
    | [("false", a2); ("true", a1)] ->
	      fprintf ff "@[<v>@[<v 2>if (%a) {@ "
	        (fun ff e -> print_exp ff e 0 avs ts single) e;
	      print_act ff a1 objs avs ts single;
	      fprintf ff "@]@ @[<v 2>} else {@ ";
	      print_act ff a2 objs avs ts single;
	      fprintf ff "@]@ }@]"
    | _ -> assert false

and print_asgn ff x e avs ts single =
  fprintf ff "@[";
  print_lhs ff x avs single;
  fprintf ff " = ";
  print_exp ff e 0 avs ts single;
  fprintf ff "@]"

let print_vd ff vd =
  let jty,jdv = java_type_default_value vd.v_type in
  fprintf ff "@[<v>";
  print_name ff jty;
  fprintf ff " %s = %s;"
    (jname_of_name (name vd.v_name))
    jdv;
  fprintf ff "@]"

let print_obj ff od =
  fprintf ff "@[<v>";
  fprintf ff "%a %a = new %a();"
    print_shortname od.cls
    print_name od.obj
    print_shortname od.cls;
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
  fprintf ff "@ %s" (jname_of_name (name vd.v_name));
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
  let name = jname_of_name n in
  fprintf ff "@[<v>@ @[<v 2>public ";
  if single then print_type ff (List.hd s.out).v_type
  else fprintf ff "%s" (n ^ "Answer");
  fprintf ff " step(@[";
  print_in ff s.inp;
  fprintf ff "@]) {@ ";
  let loc = if single then (List.hd s.out) :: s.local else s.local in
  if loc = [] then () else (print_loc ff loc; fprintf ff "@ ");
  if single then fprintf ff "@ "
  else fprintf ff "%sAnswer step_ans = new %sAnswer();@ @ " n n;
  print_act ff s.bd objs
    (List.map (fun vd -> vd.v_name) s.out) ts single;
  fprintf ff "@ @ return ";
  if single then fprintf ff "%s" (jname_of_name (Ident.name (List.hd s.out).v_name))
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
       fprintf ff "import %s.*;@\n" (String.uncapitalize m))
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
	           fprintf ff "import %s.*;@\n" (String.uncapitalize m))
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
