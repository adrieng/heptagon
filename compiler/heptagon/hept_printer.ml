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
(* The Heptagon printer *)

open Misc
open Names
open Format
open Global_printer
open Pp_tools
open Linearity
open Heptagon

let iterator_to_string i =
  match i with
    | Imap -> "map"
    | Imapi -> "mapi"
    | Ifold -> "fold"
    | Ifoldi -> "foldi"
    | Imapfold -> "mapfold"

let print_iterator ff it =
  fprintf ff "%s" (iterator_to_string it)

let print_init ff = function
  | Lno_init -> ()
  | Linit_var r -> fprintf ff "init<<%s>> " r
  | _ -> ()

let rec print_pat_init ff (pat, inits) = match pat, inits with
  | Evarpat n, i -> fprintf ff "%a%a" print_init i  print_ident n
  | Etuplepat pl, Linit_tuple il ->
      fprintf ff "@[<2>(%a)@]" (print_list_r print_pat_init """,""") (List.combine pl il)
  | Etuplepat pl, Lno_init ->
      let l = List.map (fun p -> p, Lno_init) pl in
        fprintf ff "@[<2>(%a)@]" (print_list_r print_pat_init """,""") l
  | _, _ -> assert false

let rec print_vd ff { v_ident = n; v_type = ty; v_linearity = lin; v_last = last } =
  fprintf ff "%a%a : %a%a%a"
    print_last last  print_ident n
    print_type ty  print_linearity lin  print_last_value last

and print_last ff = function
  | Last _ -> fprintf ff "last "
  | _ -> ()

and print_last_value ff = function
  | Last (Some v) -> fprintf ff " = %a" print_static_exp v
  | _ -> ()

let print_local_vars s ff l = match l with
  | [] -> ()
  | l ->
      fprintf ff "@[<4>%a@]%s@\n" (print_list_r print_vd "var "";"";") l s

let print_const_dec ff c =
  if !Compiler_options.full_type_info then
    fprintf ff "const %a : %a = %a@."
      print_qualname c.c_name print_type c.c_type print_static_exp c.c_value
  else
    fprintf ff "const %a = %a@."
      print_qualname c.c_name print_static_exp c.c_value

let print_ct_annot ff = function
  | None -> ()
  | Some ct -> fprintf ff " :: %a" print_ct ct

let rec print_params ff l =
  fprintf ff "@[<2>%a@]" (print_list_r print_static_exp "<<"","">>") l

and print_node_params ff l =
  fprintf ff "@[<2>%a@]" (print_list_r print_param "<<"","">>") l

and print_exp_tuple ff l =
  fprintf ff "@[<2>(%a)@]" (print_list_r print_exp """,""") l

and print_vd_tuple ff l =
  match l with
    | [] -> fprintf ff "()"
    | _ ->
      fprintf ff "@[<2>%a@]" (print_list_r print_vd "("";"")") l

and print_index ff idx =
  fprintf ff "@[<2>%a@]" (print_list print_static_exp "[""][""]") idx

and print_dyn_index ff idx =
  fprintf ff "@[<2>%a@]" (print_list print_exp "[""][""]") idx

and print_trunc_index ff idx =
  fprintf ff "@[<2>%a@]" (print_list print_exp "[>""<][>""<]") idx

and print_exps ff e_list =
  print_list_r print_exp "(" "," ")" ff e_list

and print_stateful ff s =
  if !Compiler_options.stateful_info && s then fprintf ff "$"

and print_exp ff e =
 if !Compiler_options.full_type_info then
    fprintf ff "(%a : %a%a%a)"
      print_exp_desc e.e_desc print_type e.e_ty
                              print_linearity e.e_linearity print_ct_annot e.e_ct_annot
  else fprintf ff "%a%a" print_exp_desc e.e_desc print_ct_annot e.e_ct_annot

and print_exp_desc ff = function
  | Evar x -> print_ident ff x
  | Elast x -> fprintf ff "last %a" print_ident x
  | Econst c -> print_static_exp ff c
  | Epre(None, e) -> fprintf ff "pre %a" print_exp e
  | Epre(Some c, e) ->
      fprintf ff "@[<2>%a fby@ %a@]" print_static_exp c  print_exp e
  | Efby(e1, e2) ->
      fprintf ff "@[<2>%a fby@ %a@]" print_exp e1  print_exp e2
  | Eapp(app, args, reset) ->
      fprintf ff "@[<2>%a@,%a@]"
        print_app (app, args) print_every reset
  | Estruct(f_e_list) ->
      print_record (print_couple print_qualname print_exp """ = """) ff f_e_list
  | Eiterator (it, { a_op = (Efun f | Enode f); a_params =f_params },
               params, pargs, args, reset) ->
    (match f_params with
      | [] ->
        fprintf ff "@[<2>%s%a %a@,<%a>%a@]%a"
          (iterator_to_string it)
          (print_list_r print_static_exp "<<"","">>") params
          print_qualname f
          print_exp_tuple pargs
          print_exp_tuple args
          print_every reset
      | _ ->
        fprintf ff "@[<2>%s%a (%a%a)@,<%a>%a@]%a"
          (iterator_to_string it)
          (print_list_r print_static_exp "<<"","">>") params
          print_qualname f print_params f_params
          print_exp_tuple pargs
          print_exp_tuple args
          print_every reset)
  | Eiterator _ -> assert false
  | Ewhen (e, c, x) ->
      fprintf ff "@[<2>(%a@ when %a(%a))@]"
        print_exp e print_qualname c print_ident x
  | Emerge (x, tag_e_list) ->
      fprintf ff "@[<2>merge %a@ %a@]"
        print_ident x print_tag_e_list tag_e_list
  | Esplit (x, e1) ->
      fprintf ff "@[<2>split %a@ %a@]"
        print_exp x  print_exp e1

and print_handler ff c =
  fprintf ff "@[<2>%a@]" (print_couple print_qualname print_exp "("" -> "")") c

and print_tag_e_list ff tag_e_list =
  fprintf ff "@[%a@]" (print_list print_handler """""") tag_e_list

and print_every ff reset =
  print_opt (fun ff id -> fprintf ff " every %a" print_exp id) ff reset

and print_app ff (app, args) =
  match app.a_op with
    | Etuple -> print_exp_tuple ff args
    (* we need a special case for '*' and '*.' as printing (_*_) is incorrect *)
    | Efun { name = n } when (n = "*" || n = "*.") ->
      let a1, a2 = assert_2 args in
      fprintf ff "@[%a@, %s@, %a@]" print_exp a1  n  print_exp a2
    | Efun ({ qual = Pervasives; name = n } as f) when (is_infix n) ->
	begin match args with
	  [a1;a2] ->
	    fprintf ff "@[(%a@, %s@, %a)@]" print_exp a1  n  print_exp a2
	| _ ->
            fprintf ff "@[%a@,%a@,%a@]"
              print_qualname f print_params app.a_params  print_exp_tuple args
	end
    | Efun f ->
        fprintf ff "@[%a@,%a@,%a@]"
          print_qualname f print_params app.a_params  print_exp_tuple args
    | Enode f ->
        print_stateful ff true;
        fprintf ff "@[%a@,%a@,%a@]"
          print_qualname f print_params app.a_params  print_exp_tuple args
    | Eifthenelse ->
      let e1, e2, e3 = assert_3 args in
        fprintf ff "@[<hv>if %a@ then %a@ else %a@]"
          print_exp e1 print_exp e2 print_exp e3
    | Efield ->
      let r = assert_1 args in
      let f = assert_1 app.a_params in
      fprintf ff "%a.%a" print_exp r print_static_exp f
    | Efield_update ->
      let r,e = assert_2 args in
      let f = assert_1 app.a_params in
        fprintf ff "@[<2>{%a with .%a =@ %a}@]"
          print_exp r print_static_exp f print_exp e
    | Earray -> fprintf ff "@[<2>%a@]" (print_list_r print_exp "["",""]") args
    | Earray_fill ->
      let e = assert_1 args in
        fprintf ff "%a@[<2>%a@]" print_exp e (print_list print_static_exp "^""^""") app.a_params
    | Eselect ->
      let e = assert_1 args in
        fprintf ff "%a%a" print_exp e print_index app.a_params
    | Eselect_slice ->
      let e = assert_1 args in
      let idx1, idx2 = assert_2 app.a_params in
        fprintf ff "%a[%a..%a]"
          print_exp e  print_static_exp idx1  print_static_exp idx2
    | Eselect_dyn ->
      let r, d, e = assert_2min args in
        fprintf ff "%a.%a default %a"
          print_exp r  print_dyn_index e  print_exp d
    | Eselect_trunc ->
      let e, idx_list = assert_1min args in
        fprintf ff "%a%a" print_exp e print_trunc_index idx_list
    | Eupdate ->
      let e1, e2, idx = assert_2min args in
          fprintf ff "@[<2>[%a with %a =@ %a]@]"
            print_exp e1 print_dyn_index idx print_exp e2
    | Econcat ->
      let e1, e2 = assert_2 args in
        fprintf ff "@[<2>%a@ @@ %a@]" print_exp e1  print_exp e2
    | Earrow ->
      let e1, e2 = assert_2 args in
        fprintf ff "@[<2>%a ->@ %a@]" print_exp e1  print_exp e2
    | Ereinit ->
        fprintf ff "@[split@,%a@]" print_exp_tuple args

let rec print_eq ff eq =
  print_stateful ff eq.eq_stateful;
  match eq.eq_desc with
    | Eeq(p, e) ->
      fprintf ff "@[<2>%a =@ %a@]" print_pat_init (p, eq.eq_inits)  print_exp e
    | Eautomaton(state_handler_list) ->
      fprintf ff "@[<v>@[<hv 2>automaton @ %a@]@,end@]"
        print_state_handler_list state_handler_list
    | Eswitch(e, switch_handler_list) ->
      fprintf ff "@[<v>@[<hv 2>switch (%a) @ %a@]@,end@]"
        print_exp e
        print_switch_handler_list switch_handler_list
    | Epresent(present_handler_list, b) ->
      fprintf ff "@[<v>@[<hv 2>present @ %a%a@]@,end@]"
        print_present_handler_list present_handler_list
        print_default b
    | Ereset(b, e) ->
      fprintf ff "@[<v>@[<hv 2>reset @ %a@]@,every %a@]"
        (print_sblock " in ") b   print_exp e
    | Eblock b ->
      fprintf ff "@[<v>do@[<v>@ @[%a@]@]@ done@]" (print_sblock " in ") b

and print_state_handler_list ff tag_act_list =
  print_list
    (fun ff sh ->
       fprintf ff "@[<v 2>state %a@ %a%a%a@]"
         print_name sh.s_state
         (print_block " do ") sh.s_block
         (print_escape_list "until") sh.s_until
         (print_escape_list "unless") sh.s_unless)
    "" "" "" ff tag_act_list

and print_escape_list unless ff esc_list = match esc_list with
  | [] -> ()
  | _ ->
      fprintf ff "@,%s %a" unless
      (print_list
         (fun ff esc ->
           let cont = if esc.e_reset then "then" else "continue" in
             fprintf ff "@,| %a %s %a"
               print_exp esc.e_cond   cont  print_name esc.e_next_state)
         "" "" "") esc_list

and print_switch_handler_list ff tag_act_list =
  print_list
    (fun ff sh ->
       fprintf ff "@[<v 2>| %a @ %a@]"
         print_qualname sh.w_name
         (print_block " do ") sh.w_block)
    "" "" "" ff tag_act_list

and print_present_handler_list ff present_act_list =
  print_list
    (fun ff ph ->
       fprintf ff "@[<v 2>| %a @ %a@]"
         print_exp ph.p_cond
         (print_block " do ") ph.p_block)
    "" "" "" ff present_act_list

and print_default ff b =
  match b.b_equs with
    | [] -> ()
    | _ -> fprintf ff "@[<v 2>default@,%a@]" (print_block " do ")  b

and print_eq_list ff = function
  | [] -> ()
  | l -> print_list_r print_eq """;""" ff l


and print_block sep ff { b_local = v_list; b_equs = eqs; b_stateful = s } =
  fprintf ff "%a@[<v>%a%a@]" print_stateful s (print_local_vars sep) v_list print_eq_list eqs

and print_sblock sep ff { b_local = v_list; b_equs = eqs } =
  match v_list with
    | [] ->
      fprintf ff "@[<v>%a@]"  print_eq_list eqs
    | _ ->
      fprintf ff "@[<v>%a@,%a@]" (print_local_vars sep) v_list print_eq_list eqs


let print_type_def ff { t_name = name; t_desc = tdesc } =
  let print_type_desc ff = function
    | Type_abs -> ()
    | Type_alias ty -> fprintf ff  " =@ %a" print_type ty
    | Type_enum tag_name_list ->
        fprintf ff " =@ %a" (print_list print_qualname """|""") tag_name_list
    | Type_struct f_ty_list ->
        fprintf ff " =@ %a" (print_record print_field) f_ty_list in
  fprintf ff "@[<2>type %a%a@]@." print_qualname name print_type_desc tdesc

let print_objective_kind ff = function
  | Obj_enforce -> fprintf ff "enforce"
  | Obj_reachable -> fprintf ff "reachable"
  | Obj_attractive -> fprintf ff "attractive"

let print_objective ff o =
  fprintf ff "@[<2>%a@ %a]"
	  print_objective_kind o.o_kind
	  print_exp o.o_exp

let print_contract ff { c_block = b;
                        c_assume = e_a;
			c_objectives = objs;
			c_controllables = c} =
  fprintf ff "@[<v2>contract@\n%a@ assume %a%a@ with (%a)@\n@]"
    (print_block " do ") b
    print_exp e_a
    (print_list print_objective "@ " "@ " "") objs 
    print_vd_tuple c

let print_node ff
    { n_name = n; n_input = ni;
      n_block = nb; n_output = no; n_contract = contract;
      n_params = params } =
  fprintf ff "@[node %a%a%a@ returns %a@]@\n%a%a@[<v2>let@ %a@]@\ntel@]@\n@."
    print_qualname n
    print_node_params params
    print_vd_tuple ni
    print_vd_tuple no
    (print_opt print_contract) contract
    (print_local_vars "") nb.b_local
    print_eq_list nb.b_equs

let print_pdesc ff pd = match pd with
  | Pnode n -> print_node ff n
  | Pconst c -> print_const_dec ff c
  | Ptype t -> print_type_def ff t

let print_open_module ff name = fprintf ff "open %s@." (modul_to_string name)

let print oc { p_opened = po; p_desc = pd; } =
  let ff = Format.formatter_of_out_channel oc in
  fprintf ff "@[<v>";
  List.iter (print_open_module ff) po;
  List.iter (print_pdesc ff) pd;
  fprintf ff "@]";
  fprintf ff "@?"
