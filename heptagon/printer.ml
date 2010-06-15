(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* the printer *)

(* $Id$ *)

open Location
open Misc
open Names
open Ident
open Heptagon
open Modules
open Static
open Format

let rec print_list ff print sep l =
  match l with
    | [] -> ()
    | [x] -> print ff x
    | x :: l ->
        print ff x;
        fprintf ff "%s@ " sep;
        print_list ff print sep l

(* Infix chars are surrounded by parenthesis *)
let is_infix =
  let module StrSet = Set.Make(String) in
  let set_infix =
    List.fold_right
      StrSet.add
      ["or"; "quo"; "mod"; "land"; "lor"; "lxor"; "lsl"; "lsr"; "asr"]
      StrSet.empty in
  fun s -> StrSet.mem s set_infix

let print_name ff s =
  let c = String.get s 0 in
  let s = if is_infix s then "(" ^ s ^ ")"
  else match c with
    | 'a' .. 'z' | 'A' .. 'Z' | '_' | '`' -> s
    | '*' -> "( " ^ s ^ " )"
    | _ -> if s = "()" then s else "(" ^ s ^ ")" in
  fprintf ff "%s" s

let print_longname ff ln =
  let ln = currentname ln in
  match ln with
    | Name(m) -> print_name ff m
    | Modname({ qual = "Pervasives"; id = m }) ->
        print_name ff m
    | Modname({ qual = m1; id = m2 }) ->
        fprintf ff "%s." m1; print_name ff m2

let print_ident ff id =
  fprintf ff "%s" (name id)

let print_iterator ff it =
  fprintf ff "%s" (iterator_to_string it)

let rec print_pat ff = function
  | Evarpat(n) -> print_ident ff n
  | Etuplepat(pat_list) ->
      fprintf ff "@[(";
      print_list ff print_pat "," pat_list;
      fprintf ff ")@]"

let rec print_base_type ff = function
  | Tint -> fprintf ff  "int"
  | Tbool -> fprintf ff "bool"
  | Tfloat -> fprintf ff  "float"
  | Tid(id) -> print_longname ff id
  | Tarray(ty, e) ->
      print_base_type ff ty;
      fprintf ff "^";
      print_size_exp ff e;

and print_type ff = function
  | Tbase(base_ty) -> print_base_type ff base_ty
  | Tprod(ty_list) ->
      fprintf ff "@[(";
      print_list ff print_type " *" ty_list;
      fprintf ff ")@]"

and print_c ff = function
  | Cint i -> fprintf ff "%d" i
  | Cfloat f -> fprintf ff "%f" f
  | Cconstr(tag) -> print_longname ff tag
  | Cconst_array (n, c) ->
      print_c ff c;
      fprintf ff "^";
      print_size_exp ff n

and print_vd ff { v_name = n; v_type = ty; v_last = last } =
  fprintf ff "@[<v>";
  begin match last with Last _ -> fprintf ff "last " | _ -> () end;
  print_ident ff n;
  fprintf ff ": ";
  print_base_type ff ty;
  begin
    match last with Last(Some(v)) -> fprintf ff "= ";print_c ff v
      | _ -> ()
  end;
  fprintf ff "@]"

and print_exps ff e_list =
  fprintf ff "@[("; print_list ff print_exp "," e_list; fprintf ff ")@]"

and print_exp ff e =
  if !Misc.full_type_info then fprintf ff "(";
  begin match e.e_desc with
    | Evar x -> print_ident ff x
    | Econstvar x -> print_name ff x
    | Elast x -> fprintf ff "last "; print_ident ff x
    | Econst c -> print_c ff c
    | Eapp({ a_op = op }, e_list) -> print_op ff op e_list
    | Etuple(e_list) ->
        fprintf ff "@[(";
        print_list ff print_exp "," e_list;
        fprintf ff ")@]"
    | Efield(e, field) ->
        print_exp ff e; fprintf ff ".";
        print_longname ff field
    | Estruct(f_e_list) ->
        fprintf ff "@[<v 1>{";
        print_list ff
          (fun ff (field, e) -> print_longname ff field;fprintf ff " = ";
             print_exp ff e)
          ";" f_e_list;
        fprintf ff "}@]"
    | Earray(e_list) ->
        fprintf ff "@[[";
        print_list ff print_exp "," e_list;
        fprintf ff "]@]"
    | Ereset_mem(y,v,res) ->
	fprintf ff "@[reset_mem ";
	print_ident ff y;
	fprintf ff " = ";
	print_exp ff v;
	fprintf ff " every ";
	print_ident ff res;
	fprintf ff "@]"
  end;
  if !Misc.full_type_info then fprintf ff " : %a)" print_type e.e_ty

and print_call_params ff = function
  | [] -> ()
  | l -> 
      fprintf ff "<<";
      print_list ff print_size_exp "," l;
      fprintf ff ">>"

and print_op ff op e_list =
  match op, e_list with
    | Epre(None), [e] -> fprintf ff "pre "; print_exp ff e
    | Epre(Some(c)), [e] -> print_c ff c; fprintf ff " fby "; print_exp ff e
    | Efby, [e1;e2] -> print_exp ff e1; fprintf ff " fby "; print_exp ff e2
    | Earrow, [e1;e2] -> print_exp ff e1; fprintf ff " -> "; print_exp ff e2
    | Eifthenelse,[e1;e2;e3] ->
        fprintf ff "@["; fprintf ff "if "; print_exp ff e1;
        fprintf ff "@ then@ "; print_exp ff e2;
        fprintf ff "@ else@ "; print_exp ff e3;
        fprintf ff "@]"
    | Enode(f, params), e_list ->
        print_longname ff f;
	print_call_params ff params;
        fprintf ff "(@["; print_list ff print_exp "," e_list;
        fprintf ff ")@]"
    | Eevery(f,params), e_list ->
        print_longname ff f;
	print_call_params ff params;
        fprintf ff "(@["; print_list ff print_exp "," e_list;
        fprintf ff ")@]"
    | Eop(f, params), e_list ->
        print_longname ff f;
	print_call_params ff params;
        fprintf ff "(@["; print_list ff print_exp "," e_list;
        fprintf ff ")@]"
    | Erepeat, [e1; e2] ->
	print_exp ff e1;
	fprintf ff "^";
	print_exp ff e2
    | Eselect idx_list, [e] -> 
	print_exp ff e;
	fprintf ff "[";
	print_list ff print_size_exp "][" idx_list;
	fprintf ff "]"
    | Eselect_dyn, e::defe::idx_list ->
	fprintf ff "@[(";
	print_exp ff e;
	fprintf ff "[";
	print_list ff print_exp "][" idx_list;
	fprintf ff "] default ";
	print_exp ff defe;
	fprintf ff ")@]"
    | Eupdate idx_list, [e1;e2] ->
	fprintf ff "(@[";
	print_exp ff e1;
	fprintf ff " with [";
	print_list ff print_size_exp "][" idx_list;
	fprintf ff "] = ";
	print_exp ff e2;
	fprintf ff ")@]"
    | Eselect_slice, [e; idx1; idx2] ->
	print_exp ff e;
	fprintf ff "[";
	print_exp ff idx1;
	fprintf ff "..";
	print_exp ff idx2;
	fprintf ff "]"	
    | Eiterator (it, op, params, reset), e::e_list -> 
	fprintf ff "("; 
	print_iterator ff it;
	fprintf ff " ";
	(match params with
	   | [] -> print_longname ff op
	   | l -> 
	       fprintf ff "(";
	       print_longname ff op;
	       print_call_params ff params;
	       fprintf ff ")"
	);
	fprintf ff " <<";
	print_exp ff e;
	fprintf ff ">>) (@[";
	print_list ff print_exp "," e_list;
	fprintf ff ")@]";
	(match reset with 
	   | None -> ()
	   | Some r -> fprintf ff " every %a" print_exp r
	)
    | Econcat, [e1;e2] -> 
	fprintf ff "@[";
	print_exp ff e1;
	fprintf ff " @@ ";
	print_exp ff e2;
	fprintf ff "@]"
    | Ecopy, [e] -> 
	fprintf ff "@[copy (";
	print_exp ff e;
	fprintf ff ")@]"
    | Efield_update f, [e1;e2] -> 
	fprintf ff "(@[";
	print_exp ff e1;
	fprintf ff " with .";
	print_longname ff f;
	fprintf ff " = ";
	print_exp ff e2;
	fprintf ff ")@]"
    | Eflatten n, e_list ->
	fprintf ff "@[(flatten ";
	print_longname ff n;
	fprintf ff ")(";
	print_list ff print_exp "," e_list;
	fprintf ff ")@]"
    | Emake n, e_list -> 
	fprintf ff "@[(make ";
	print_longname ff n;
	fprintf ff ")(";
	print_list ff print_exp "," e_list;
	fprintf ff ")@]"
    | _ -> assert false

let rec print_eq ff eq =
  match eq.eq_desc with
    | Eeq(p, e) ->
        fprintf ff "@[<hov 2>";
        print_pat ff p;
        fprintf ff " =@ ";
        print_exp ff e;
        fprintf ff "@]"
    | Eautomaton(state_handler_list) ->
        fprintf ff "@[<v>automaton@,";
        fprintf ff "@[<v>";
        print_list ff print_state_handler "" state_handler_list;
        fprintf ff "@]@,";
        fprintf ff "end@]"
    | Eswitch(e, switch_handler_list) ->
        fprintf ff "@[<v>switch ";
        print_exp ff e;
        fprintf ff "@,@[<v>";
        print_list ff print_switch_handler "" switch_handler_list;
        fprintf ff "@]@,";
        fprintf ff "end@]"
    | Epresent(present_handler_list, b) ->
        fprintf ff "@[<v>present@,";
        print_list ff print_present_handler "" present_handler_list;
        if b.b_equs <> [] then begin
          fprintf ff "  @[<v 2>default@,";
          print_block ff b;
          fprintf ff "@]"
        end;
        fprintf ff "@,end@]"
    | Ereset(eq_list, e) ->
        fprintf ff "@[<v>reset@,";
        fprintf ff "  @[<v>";
        print_eq_list ff eq_list;
        fprintf ff "@]";
        fprintf ff "@,every ";
        print_exp ff e;
        fprintf ff "@]"

and print_eq_list ff = function
  | [] -> ()
  | [eq] -> print_eq ff eq;fprintf ff ";"
  | eq :: l -> print_eq ff eq;fprintf ff ";@,";print_eq_list ff l

and print_state_handler ff
    { s_state = s; s_block = b; s_until = until; s_unless = unless } =
  fprintf ff "  @[<v 2>state ";
  fprintf ff "%s@," s;
  print_block ff b;
  if until <> [] then
    begin
      fprintf ff "@,@[<v 2>until ";
      print_list ff print_escape "" until;
      fprintf ff "@]"
    end;
  if unless <> [] then
    begin
      fprintf ff "@,@[<v 2>unless ";
      print_list ff print_escape " " unless;
      fprintf ff "@]"
    end;
  fprintf ff "@]"

and print_switch_handler ff { w_name = tag; w_block = b } =
  fprintf ff "  @[<v 2>| ";
  print_longname ff tag;
  fprintf ff "@,";
  print_block ff b;
  fprintf ff "@]"

and print_present_handler ff { p_cond = e; p_block = b } =
  fprintf ff "  @[<v 2>| ";
  print_exp ff e;
  fprintf ff "@,";
  print_block ff b;
  fprintf ff "@]"

and print_escape ff { e_cond = e; e_reset = r; e_next_state = ns} =
  fprintf ff "@,| ";
  print_exp ff e;
  if r then fprintf ff " then " else fprintf ff " continue ";
  print_name ff ns

and print_block ff { b_local = v_list; b_equs = eqs; b_defnames = defnames } =
  if v_list <> [] then
    begin
      fprintf ff "@[<v 2>var ";
      print_list ff print_vd ";" v_list;
      fprintf ff "@]@,"
    end;
  (*   (\* DEBUG *\) *)
  (*   fprintf ff "@[<hov 2>defines @,"; *)
  (*   Env.iter (fun n t -> fprintf ff "%s," n) defnames; *)
  (*   fprintf ff "@]@\n"; *)
  (*   (\* END DEBUG *\) *)
  fprintf ff "@[<v 2>do@,";
  print_eq_list ff eqs;
  fprintf ff "@]"

let print_type_def ff { t_name = name; t_desc = tdesc } =
  match tdesc with
    | Type_abs -> fprintf ff "@[type %s@\n@]" name
    | Type_enum(tag_name_list) ->
        fprintf ff "@[type %s = " name;
        print_list ff print_name "| " tag_name_list;
        fprintf ff "@\n@]"
    | Type_struct(f_ty_list) ->
        fprintf ff "@[type %s = " name;
        fprintf ff "@[<v 1>{";
        print_list ff
          (fun ff (field, ty) ->
             print_name ff field;
             fprintf ff ": ";
             print_base_type ff ty) ";" f_ty_list;
        fprintf ff "}@]@.@]"

let print_const_dec ff c =
  fprintf ff "@[const ";
  print_name ff c.c_name;
  fprintf ff " : ";
  print_base_type ff c.c_type;
  fprintf ff " = ";
  print_size_exp ff c.c_value;
  fprintf ff "@.@]"

let print_contract ff {c_local = l;
                       c_eq = eqs;
                       c_assume = e_a;
                       c_enforce = e_g;
                       c_controllables = cl } =
  if l <> [] then begin
    fprintf ff "@[<v 2>contract@\n";
    fprintf ff "@[<hov 4>var ";
    print_list ff print_vd ";" l;
    fprintf ff ";@]@\n"
  end;
  if eqs <> [] then begin
    fprintf ff "@[<v 2>let @,";
    print_eq_list ff eqs;
    fprintf ff "@]"; fprintf ff "tel@\n"
  end;
  fprintf ff "assume %a@;enforce %a@;with (@[<hov>"
    print_exp e_a
    print_exp e_g;
  print_list ff print_vd ";" cl;
  fprintf ff "@])@]@\n"

let print_node_params ff = function
  | [] -> ()
  | l -> 
      fprintf ff "<<";
      print_list ff print_name "," l;
      fprintf ff ">>"

let print_node ff
    { n_name = n; n_statefull = statefull; n_input = ni;
      n_local = nl; n_output = no; n_contract = contract; n_equs = ne;
      n_params = params; } =
  fprintf ff "@[<v 2>%s " (if statefull then "node" else "fun");
  print_name ff n; 
  print_node_params ff params;
  fprintf ff "(@[";
  print_list ff print_vd ";" ni;
  fprintf ff "@]) returns (@[";
  print_list ff print_vd ";" no;
  fprintf ff "@])@,";
  optunit (print_contract ff) contract;
  if nl <> [] then begin
    fprintf ff "@[<hov 4>var ";
    print_list ff print_vd ";" nl;
    fprintf ff ";@]@,"
  end;
  fprintf ff "@[<v 2>let @,";
  print_eq_list ff ne;
  fprintf ff "@]@;"; fprintf ff "tel";fprintf ff "@.@]"

let print_open_module ff name =
  fprintf ff "@[open ";
  print_name ff name;
  fprintf ff "@.@]"

let ptype oc ty =
  let ff = formatter_of_out_channel oc in
  print_type ff ty; fprintf ff "@?"

let print oc { p_opened = po; p_types = pt; p_nodes = pn; p_consts = pc } =
  let ff = formatter_of_out_channel oc in
  List.iter (print_open_module ff) po;
  List.iter (print_const_dec ff) pc;
  List.iter (print_type_def ff) pt;
  List.iter (print_node ff) pn;
  fprintf ff "@?"
