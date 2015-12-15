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
open Misc
open Names
open Linearity
open Format
open Global_printer
open Pp_tools
open Minils

(** Every print_ function is boxed, that is it doesn't export break points,
    Exceptions are [list] class functions *)

(** Every print_ function is without heading carry return or white space *)

let iterator_to_string i =
  match i with
    | Imap -> "map"
    | Imapi -> "mapi"
    | Ifold -> "fold"
    | Ifoldi -> "foldi"
    | Imapfold -> "mapfold"

let rec print_pat ff = function
  | Evarpat n -> print_ident ff n
  | Etuplepat pat_list ->
      fprintf ff "@[<2>(%a)@]" (print_list_r print_pat """,""") pat_list

let print_vd ?(show_ck=false) ff { v_ident = n; v_type = ty; v_linearity = lin; v_clock = ck } =
 if show_ck || !Compiler_options.full_type_info then
    fprintf ff "%a : %a%a :: %a" print_ident n print_type ty print_linearity lin print_ck ck
  else fprintf ff "%a : %a%a" print_ident n print_type ty print_linearity lin

let print_local_vars ff = function
  | [] -> ()
  | l -> fprintf ff "@[<4>%a@]@\n" (print_list_r print_vd "var "";"";") l

let print_const_dec ff c =
  if !Compiler_options.full_type_info then
    fprintf ff "const %a : %a = %a"
      print_qualname c.c_name print_type c.c_type print_static_exp c.c_value
  else
    fprintf ff "const %a = %a"
      print_qualname c.c_name print_static_exp c.c_value;
  fprintf ff "@."


let rec print_params ff l =
  fprintf ff "@[<2>%a@]" (print_list_r print_static_exp "<<"","">>") l

and print_node_params ff l =
  fprintf ff "@[<2>%a@]" (print_list_r print_param "<<"","">>") l

and print_exp_tuple ff l =
  fprintf ff "@[<2>(%a)@]" (print_list_r print_exp """,""") l

and print_w_tuple ff l =
  fprintf ff "@[<2>(%a)@]" (print_list_r print_extvalue """,""") l

and print_vd_tuple ff l =
  fprintf ff "@[<2>%a@]" (print_list_r (print_vd ~show_ck:false) "("";"")") l

and print_full_vd_tuple ff l =
  fprintf ff "@[<2>%a@]" (print_list_r (print_vd ~show_ck:true) "("";"")") l

and print_index ff idx =
  fprintf ff "@[<2>%a@]" (print_list print_static_exp "[""][""]") idx

and print_dyn_index ff idx =
  fprintf ff "@[<2>%a@]" (print_list print_extvalue "[""][""]") idx

and print_trunc_index ff idx =
  fprintf ff "@[<2>%a@]" (print_list print_extvalue "[>""<][>""<]") idx

and print_exp ff e =
  if !Compiler_options.full_type_info then
    fprintf ff "(%a : %a%a :: %a)"
      print_exp_desc e.e_desc print_type e.e_ty print_linearity e.e_linearity print_ct e.e_ct
  else fprintf ff "%a" print_exp_desc e.e_desc

and print_every ff reset =
  print_opt (fun ff id -> fprintf ff " every %a" print_ident id) ff reset

and print_extvalue ff w =
  if !Compiler_options.full_type_info then
    fprintf ff "(%a : %a%a :: %a)"
      print_extvalue_desc w.w_desc print_type w.w_ty print_linearity w.w_linearity print_ck w.w_ck
  else fprintf ff "%a" print_extvalue_desc w.w_desc


and print_extvalue_desc ff = function
  | Wconst c -> print_static_exp ff c
  | Wvar x -> print_ident ff x
  | Wfield (w,f) -> fprintf ff "%a.%a" print_extvalue w print_qualname f
  | Wwhen (w, c, n) ->
      fprintf ff "@[<2>(%a@ when %a(%a))@]" print_extvalue w print_qualname c print_ident n
  | Wreinit (w1, w2) ->
      fprintf ff "@[reinit@,(%a, %a)@]" print_extvalue w1  print_extvalue w2

and print_exp_desc ff = function
  | Eextvalue w -> print_extvalue ff w
  | Efby ((Some c), w) -> fprintf ff "@[<2>%a fby@ %a@]" print_static_exp c print_extvalue w
  | Efby (None, w) -> fprintf ff "pre %a" print_extvalue w
  | Eapp (app, args, reset) ->
      fprintf ff "@[<2>%a@,%a@]" print_app (app, args) print_every reset
  | Emerge (x, tag_w_list) ->
      fprintf ff "@[<2>merge %a@ %a@]" print_ident x print_tag_w_list tag_w_list
  | Ewhen (e,c,x) ->
      fprintf ff "@[<2>(%a@ when %a(%a))@]" print_exp e print_qualname c print_ident x
  | Estruct f_w_list ->
      print_record (print_couple print_qualname print_extvalue """ = """) ff f_w_list
  | Eiterator (it, f, params, pargs, args, reset) ->
      fprintf ff "@[<2>(%s (%a)<<%a>>)@,(%a)%a@]%a"
        (iterator_to_string it)
        print_app (f, [])
        (print_list_r print_static_exp """, """) params
        print_w_tuple pargs
        print_w_tuple args
        print_every reset

and print_app ff (app, args) =
  match app.a_op with
    | Eequal ->
      let e1, e2 = assert_2 args in
        fprintf ff "@[<2>%a@ = %a@]" print_extvalue e1  print_extvalue e2
    | Efun ({ qual = Pervasives; name = n } as f) when (is_infix n) ->
	begin match args with
	  [a1;a2] ->
	    fprintf ff "@[(%a@, %s@, %a)@]"
	      print_extvalue a1
	      n
	      print_extvalue a2
	| _ ->
            fprintf ff "@[%a@,%a@,%a@]"
              print_qualname f print_params app.a_params  print_w_tuple args
	end
    | Efun f | Enode f ->
        fprintf ff "@[%a@,%a@,%a@]"
          print_qualname f print_params app.a_params  print_w_tuple args
    | Eifthenelse ->
      let e1, e2, e3 = assert_3 args in
        fprintf ff "@[<hv>if %a@ then %a@ else %a@]"
          print_extvalue e1 print_extvalue e2 print_extvalue e3
    | Efield_update ->
      let r,e = assert_2 args in
      let f = assert_1 app.a_params in
        fprintf ff "@[<2>{%a with .%a =@ %a}@]"
          print_extvalue r print_static_exp f print_extvalue e
    | Earray -> fprintf ff "@[<2>%a@]" (print_list_r print_extvalue "["";""]") args
    | Earray_fill ->
      let e = assert_1 args in
      let n_list = app.a_params in
        fprintf ff "%a@[<2>%a@]" print_extvalue e (print_list print_static_exp "^""^""") n_list
    | Eselect ->
      let e = assert_1 args in
        fprintf ff "%a%a" print_extvalue e print_index app.a_params
    | Eselect_slice ->
      let e = assert_1 args in
      let idx1, idx2 = assert_2 app.a_params in
        fprintf ff "%a[%a..%a]"
          print_extvalue e  print_static_exp idx1  print_static_exp idx2
    | Eselect_dyn ->
      let r, d, e = assert_2min args in
        fprintf ff "%a%a default %a"
          print_extvalue r  print_dyn_index e  print_extvalue d
    | Eselect_trunc ->
      let e, idx_list = assert_1min args in
        fprintf ff "%a%a" print_extvalue e print_trunc_index idx_list
    | Eupdate ->
      let e1, e2, idx = assert_2min args in
          fprintf ff "@[<2>(%a with %a =@ %a)@]"
            print_extvalue e1 print_dyn_index idx print_extvalue e2
    | Econcat ->
      let e1, e2 = assert_2 args in
        fprintf ff "@[<2>%a@ @@ %a@]" print_extvalue e1  print_extvalue e2

and print_handler ff c =
  fprintf ff "@[<2>%a@]" (print_couple print_qualname print_extvalue "("" -> "")") c

and print_tag_w_list ff tag_w_list =
  fprintf ff "@[%a@]" (print_list print_handler """""") tag_w_list


and print_eq ff { eq_lhs = p; eq_rhs = e; eq_base_ck = base_ck } =
  if !Compiler_options.full_type_info
  then fprintf ff "@[<2>%a :: %a =@ %a@]"
    print_pat p  print_ck base_ck  print_exp e
  else fprintf ff "@[<2>%a =@ %a@]" print_pat p  print_exp e


and print_eqs ff = function
  | [] -> ()
  | l -> fprintf ff "@[<v2>let@ %a@]@\ntel" (print_list_r print_eq """;""") l

let print_open_module ff name = fprintf ff "open %s@." (modul_to_string name)

let print_type_dec ff { t_name = name; t_desc = tdesc } =
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
	  print_extvalue o.o_exp

let print_contract ff { c_local = l; c_eq = eqs;
                        c_assume = e_a;
			c_objectives = objs;
			c_controllables = c;} =
  fprintf ff "@[<v2>contract@\n%a%a@ assume %a%a@ with %a@\n@]"
    print_local_vars l
    print_eqs eqs
    print_extvalue e_a
    (print_list print_objective "@ " "@ " "") objs 
    print_vd_tuple c


let print_node ff { n_name = n; n_input = ni; n_output = no;
                    n_contract = contract; n_local = nl;
                    n_equs = ne; n_params = params } =
  fprintf ff "@[node %a%a%a@ returns %a@]@\n%a%a%a@]@\n@."
    print_qualname n
    print_node_params params
    print_vd_tuple ni
    print_vd_tuple no
    (print_opt print_contract) contract
    print_local_vars nl
    print_eqs ne


let print oc { p_opened = pm; p_desc = pd } =
  let print_program_desc ff pd = match pd with
    | Pnode n -> print_node ff n
    | Ptype t -> print_type_dec ff t
    | Pconst c -> print_const_dec ff c
  in
  let ff = formatter_of_out_channel oc in
  List.iter (print_open_module ff) pm;
  List.iter (print_program_desc ff) pd;
  fprintf ff "@?"
