open Minils
open Names
open Ident
open Types
open Static
open Format
open Signature
open Pp_tools


let iterator_to_string i = 
  match i with 
    | Imap -> "map"
    | Ifold -> "fold"
    | Imapfold -> "mapfold"


let rec print_pat ff = function
  | Evarpat n -> print_ident ff n
  | Etuplepat pat_list ->
      fprintf ff "@[%a@]" (print_list_r print_pat "("","")") pat_list

let rec print_ck ff = function
  | Cbase -> fprintf ff "base"
  | Con (ck, c, n) ->
      fprintf ff "%a on %a(%a)" print_ck ck print_longname c print_ident n
  | Cvar { contents = Cindex n } -> fprintf ff "base"
  | Cvar { contents = Clink ck } -> print_ck ff ck

let rec print_clock ff = function
  | Ck ck -> print_ck ff ck
  | Cprod ct_list ->
      fprintf ff "@[%a@]" (print_list_r print_clock "("" *"")") ct_list

let print_vd ff { v_name = n; v_type = ty; v_clock = ck } =
  fprintf ff "@[<v>%a : %a :: %a@]" print_ident n print_type ty print_ck ck
  
let rec print_c ff = function
  | Cint i -> fprintf ff "%d" i
  | Cfloat f -> fprintf ff "%f" f
  | Cconstr tag -> print_longname ff tag
  | Carray (n, c) -> fprintf ff "@[%a^%a@]" print_c c print_size_exp n

let print_params ff l = print_list_l print_size_exp "<<"","">>" ff l

let print_node_params ff l = print_list_l print_param "<<"","">>" ff l

let print_node_args ff l = print_list_l print_vd "("","")" ff l

let print_index ff idx = print_list print_size_exp "[""][""]" ff idx

let rec print_dyn_index ff idx = print_list print_exp "[""][""]" ff idx

and print_args ff e_list =
  fprintf ff "@[%a@]" (print_list_r print_exp "("","")") e_list

and print_op ff op =
  fprintf ff "%a %a" print_longname op.op_name print_params op.op_params
  
and print_exp ff e =
  if !Misc.full_type_info then 
    fprintf ff "@[<hov2>(%a@ : %a)@]" print_exp_desc e.e_desc print_type e.e_ty
  else fprintf ff "%a" print_exp_desc e.e_desc
  
and print_every ff reset =
  print_opt (fun ff id -> fprintf ff " every %a" print_ident id) ff reset 

and print_exp_desc ff = function
  | Evar x -> print_ident ff x
  | Econstvar x -> print_name ff x
  | Econst c -> print_c ff c
  | Efby ((Some c), e) ->
      (print_c ff c; fprintf ff " fby "; print_exp ff e)
  | Efby (None, e) -> (fprintf ff "pre "; print_exp ff e)
  | Ecall (op, args, reset) ->
      fprintf ff "%a %a%a"
        print_op op print_args args print_every reset
  | Ewhen (e, c, n) ->
      fprintf ff "@[(%a when %a(%a))@]"
        print_exp e print_longname c print_ident n
  | Eifthenelse (e1, e2, e3) ->
      fprintf ff "@[<hv>if %a@ then %a@ else %a@]"
        print_exp e1 print_exp e2 print_exp e3
  | Emerge (x, tag_e_list) ->
      fprintf ff "@[<hov2>merge %a@ @[%a@]@]"
        print_ident x print_tag_e_list tag_e_list
  | Etuple e_list -> 
      fprintf ff "@[%a@]" (print_list_r print_exp "("","")") e_list
  | Efield (e, field) ->
      fprintf ff "%a.%a" print_exp e print_longname field
  | Estruct f_e_list ->
      print_record (print_couple print_longname print_exp """ =""") ff f_e_list
  | Earray e_list ->
      fprintf ff "@[%a@]" (print_list_r print_exp "["";""]") e_list
  | Earray_op(array_op) ->
      print_array_op ff array_op
  | Efield_update (f, e1, e2) ->
      fprintf ff "@[%a@ with .%a =@ %a@]"
        print_exp e1 print_longname f print_exp e2


and print_array_op ff = function
  | Erepeat (n, e) -> (print_exp ff e; fprintf ff "^"; print_size_exp ff n)
  | Eselect (idx, e) -> fprintf ff "@[%a%a@]" print_exp e print_index idx
  | Eselect_dyn (idx, _, e1, e2) ->
      fprintf ff "@[%a%a default %a@]"
        print_exp e1 print_dyn_index idx print_exp e2
  | Eupdate (idx, e1, e2) ->
      fprintf ff "@[%a with %a = %a@]" print_exp e1 print_index idx print_exp e2
  | Eselect_slice (idx1, idx2, e) ->
      fprintf ff "@[%a[%a..%a]@]"
        print_exp e print_size_exp idx1 print_size_exp idx2
  | Econcat (e1, e2) -> fprintf ff "%a @@ %a" print_exp e1 print_exp e2
  | Eiterator (it, f, params, n, e_list, r) ->
     fprintf ff "(%s (%a%a) <<%a>>)@ @[%a@]%a"
       (iterator_to_string it) print_longname f print_params params
       print_size_exp n (print_list_l print_exp "("","")") e_list print_every r

and print_tag_e_list ff tag_e_list =
  fprintf ff "@[%a@]"
    (print_list
      (print_couple print_longname print_exp "("" ->"")") """""") tag_e_list


let print_eq ff { eq_lhs = p; eq_rhs = e } =
  if !Misc.full_type_info
  then fprintf ff "@[<hov2>%a :: %a =@ %a;@]"
         print_pat p print_ck e.e_ck print_exp e
  else fprintf ff "@[<hov2>%a =@ %a;@]" print_pat p print_exp e


let print_eqs ff l =
  fprintf ff "@\n@[<hv2>let@ %a@]@ tel" (print_list print_eq """""") l

let print_open_module ff name = fprintf ff "@[open %a@]@." print_name name

let rec print_type_def ff { t_name = name; t_desc = tdesc } =
  fprintf ff "@[type %s%a@]@." name print_type_desc tdesc

and print_field ff field =
  fprintf ff "%a:@ %a" print_name field.f_name print_type field.f_type
  
and print_type_desc ff = function
  | Type_abs -> ()
  | Type_enum tag_name_list ->
      fprintf ff " =@ %a" (print_list print_name """|""") tag_name_list
  | Type_struct f_ty_list ->
      fprintf ff " =@ %a"
        (print_record print_field) f_ty_list

let print_contract ff
    { c_local = l; c_eq = eqs;
      c_assume = e_a; c_enforce = e_g; c_controllables = cl } =
  fprintf ff "@\n@[<v2>";
  (if l <> []
    then
      (fprintf ff "contract\n";
        fprintf ff "@[<hov 4>var ";
        print_list_l print_vd """;""" ff l;
        fprintf ff ";@]\n")
    else ();
    if eqs <> []
    then
      (fprintf ff "@[<v 2>let @,";
        print_eqs ff eqs;
        fprintf ff "@]";
        fprintf ff "tel\n")
    else ();
    fprintf ff "assume@ %a@;enforce@ %a with (" print_exp e_a print_exp e_g;
    print_list_l print_vd """;""" ff cl;
    fprintf ff ")@]")


let print_node ff
    { n_name = n; n_input = ni; n_output = no;
      n_contract = contract; n_local = nl; n_equs = ne; n_params = params } =
  fprintf ff "@[<hov2>node %s%a%a@ returns %a%a@\n%a%a@]@."
    n
    print_node_params params
    print_node_args ni
    print_node_args no
    (print_opt print_contract) contract
    (print_list_l print_vd "var "";"";") nl
    print_eqs ne


let print_exp oc e =
  let ff = formatter_of_out_channel oc in (print_exp ff e; fprintf ff "@.")

let print_type oc ty =
  let ff = formatter_of_out_channel oc in (print_type ff ty; fprintf ff "@?")

let print_clock oc ct =
  let ff = formatter_of_out_channel oc
  in (print_clock ff ct; fprintf ff "@?")

let print oc { p_opened = pm; p_types = pt; p_nodes = pn } =
  let ff = formatter_of_out_channel oc
  in
  (List.iter (print_open_module ff) pm;
    List.iter (print_type_def ff) pt;
    List.iter (print_node ff) pn;
    fprintf ff "@?")
