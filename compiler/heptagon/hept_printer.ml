(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* The Heptagon printer *)

open Location
open Misc
open Names
open Ident
open Modules
open Static
open Format
open Pp_tools
open Types
open Signature
open Heptagon

let iterator_to_string i =
  match i with
    | Imap -> "map"
    | Ifold -> "fold"
    | Imapfold -> "mapfold"

let print_iterator ff it =
  fprintf ff "%s" (iterator_to_string it)

let rec print_pat ff = function
  | Evarpat(n) -> print_ident ff n
  | Etuplepat(pat_list) ->
      print_list_r print_pat "(" "," ")" ff pat_list

and print_vd ff { v_ident = n; v_type = ty; v_last = last } =
  fprintf ff "@[<v>";
  begin match last with Last _ -> fprintf ff "last " | _ -> () end;
  print_ident ff n;
  fprintf ff ": ";
  print_type ff ty;
  begin
    match last with Last(Some(v)) -> fprintf ff "= ";print_static_exp ff v
      | _ -> ()
  end;
  fprintf ff "@]"

and print_exps ff e_list =
  print_list_r print_exp "(" "," ")" ff e_list

and print_exp ff e =
  if !Misc.full_type_info then fprintf ff "(";
  begin match e.e_desc with
    | Evar x -> print_ident ff x
    | Elast x -> fprintf ff "last "; print_ident ff x
    | Econst c -> print_static_exp ff c
    | Epre(None, e) -> fprintf ff "pre "; print_exp ff e
    | Epre(Some c, e) -> print_static_exp ff c; fprintf ff " fby "; print_exp ff e
    | Efby(e1, e2) -> print_exp ff e1; fprintf ff " fby "; print_exp ff e2
    | Eapp({ a_op = op; a_params = params }, e_list, r) ->
        print_op ff op params e_list;
        (match r with
           | None -> ()
           | Some r -> fprintf ff " every %a" print_exp r
        )
    | Estruct(f_e_list) ->
        print_list_r
          (fun ff (field, e) -> print_longname ff field;fprintf ff " = ";
             print_exp ff e)
          "{" ";" "}" ff f_e_list;
        fprintf ff "}@]"
    | Eiterator (it, { a_op = (Efun ln|Enode ln); a_params = params },
                 n, e_list, reset) ->
        fprintf ff "(";
        print_iterator ff it;
        fprintf ff " ";
        (match params with
           | [] -> print_longname ff ln
           | l ->
               fprintf ff "(";
               print_longname ff ln;
               print_call_params ff params;
               fprintf ff ")"
        );
        fprintf ff " <<";
        print_static_exp ff n;
        fprintf ff ">>) ";
        print_exps ff e_list;
        (match reset with
           | None -> ()
           | Some r -> fprintf ff " every %a" print_exp r
        )
  end;
  if !Misc.full_type_info then fprintf ff " : %a)" print_type e.e_ty

and print_call_params ff = function
  | [] -> ()
  | l -> print_list_r print_static_exp "<<" "," ">>" ff l

and print_op ff op params e_list =
  match op, params, e_list with
    | Earrow, _, [e1;e2] -> print_exp ff e1; fprintf ff " -> "; print_exp ff e2
    | Eifthenelse, _, [e1;e2;e3] ->
        fprintf ff "@["; fprintf ff "if "; print_exp ff e1;
        fprintf ff "@ then@ "; print_exp ff e2;
        fprintf ff "@ else@ "; print_exp ff e3;
        fprintf ff "@]"
    | Etuple, _, e_list -> print_exps ff e_list
    | Earray, _, e_list ->
        print_list_r print_exp "[" "," "]" ff e_list
    | (Efun f|Enode f), params, e_list ->
        print_longname ff f;
        print_call_params ff params;
        print_exps ff e_list
    | Efield, [field], [e] ->
        print_exp ff e; fprintf ff ".";
        print_static_exp ff field
    | Efield_update, [se], [e1;e2] ->
        fprintf ff "(@[";
        print_exp ff e1;
        fprintf ff " with .";
        print_static_exp ff se;
        fprintf ff " = ";
        print_exp ff e2;
        fprintf ff ")@]"
    | Earray_fill, [se], [e] ->
        print_exp ff e;
        fprintf ff "^";
        print_static_exp ff se
    | Eselect, idx_list, [e] ->
        print_exp ff e;
        print_list_r print_static_exp "[" "][" "]" ff idx_list
    | Eselect_dyn, _, e::defe::idx_list ->
        fprintf ff "@[(";
        print_exp ff e;
        print_list_r print_exp "[" "][" "] default " ff idx_list;
        print_exp ff defe;
        fprintf ff ")@]"
    | Eupdate, idx_list, [e1;e2] ->
        fprintf ff "(@[";
        print_exp ff e1;
        fprintf ff " with ";
        print_list_r print_static_exp "[" "][" "]" ff idx_list;
        fprintf ff " = ";
        print_exp ff e2;
        fprintf ff ")@]"
    | Eselect_slice, [idx1;idx2], [e] ->
        print_exp ff e;
        fprintf ff "[";
        print_static_exp ff idx1;
        fprintf ff "..";
        print_static_exp ff idx2;
        fprintf ff "]"
    | Econcat, _, [e1;e2] ->
        fprintf ff "@[";
        print_exp ff e1;
        fprintf ff " @@ ";
        print_exp ff e2;
        fprintf ff "@]"

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
        print_list print_state_handler "" "" "" ff state_handler_list;
        fprintf ff "@]@,";
        fprintf ff "end@]"
    | Eswitch(e, switch_handler_list) ->
        fprintf ff "@[<v>switch ";
        print_exp ff e;
        fprintf ff "@,@[<v>";
        print_list print_switch_handler "" "" "" ff switch_handler_list;
        fprintf ff "@]@,";
        fprintf ff "end@]"
    | Epresent(present_handler_list, b) ->
        fprintf ff "@[<v>present@,";
        print_list print_present_handler "" "" "" ff present_handler_list;
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
      print_list print_escape "" "" "" ff until;
      fprintf ff "@]"
    end;
  if unless <> [] then
    begin
      fprintf ff "@,@[<v 2>unless ";
      print_list_r print_escape "" " " "" ff unless;
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
      print_list_r print_vd "" ";" "" ff v_list;
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
        print_list_r print_name "" "| " "" ff tag_name_list;
        fprintf ff "@\n@]"
    | Type_struct(f_ty_list) ->
        fprintf ff "@[type %s = " name;
        print_list_r
          (fun ff { f_name = field; f_type = ty } ->
             print_name ff field;
             fprintf ff ": ";
             print_type ff ty) "{" ";" "}" ff f_ty_list;
        fprintf ff "@.@]"

let print_const_dec ff c =
  fprintf ff "@[const ";
  print_name ff c.c_name;
  fprintf ff " : ";
  print_type ff c.c_type;
  fprintf ff " = ";
  print_static_exp ff c.c_value;
  fprintf ff "@.@]"

let print_contract ff {c_local = l;
                       c_eq = eqs;
                       c_assume = e_a;
                       c_enforce = e_g } =
  if l <> [] then begin
    fprintf ff "@[<v 2>contract@\n";
    fprintf ff "@[<hov 4>var ";
    print_list_r print_vd "" ";" "" ff l;
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
  fprintf ff "@])@]@\n"

let print_node_params ff = function
  | [] -> ()
  | l -> print_list_r print_param "<<" "," ">>" ff l

let print_node ff
    { n_name = n; n_input = ni;
      n_local = nl; n_output = no; n_contract = contract; n_equs = ne;
      n_params = params; } =
  fprintf ff "@[<v 2>node ";
  print_name ff n;
  fprintf ff "@[%a@]" print_node_params params;
  fprintf ff "@[%a@]" (print_list_r print_vd "(" ";" ")") ni;
  fprintf ff " returns ";
  fprintf ff "@[%a@]" (print_list_r print_vd "(" ";" ")") no;
  fprintf ff "@,";
  optunit (print_contract ff) contract;
  if nl <> [] then begin
    fprintf ff "@[<hov 4>var ";
    print_list_r print_vd "" ";" "" ff nl;
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
