open Minils
open Names
open Ident
open Types
open Static
open Format
open Pp_tools


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
  fprintf ff "@[<v>%a : %a at %a@]" print_ident n print_type ty print_ck ck
  
let rec print_c ff = function
  | Cint i -> fprintf ff "%d" i
  | Cfloat f -> fprintf ff "%f" f
  | Cconstr tag -> print_longname ff tag
  | Carray (n, c) -> fprintf ff "@[%a^%a@]" print_c c print_size_exp n

let print_params ff = function
  | [] -> ()
  | l -> print_list_r print_size_exp "<<"","">>" ff l

let rec print_args ff e_list =
  fprintf ff "@[%a@]" (print_list_r print_exp "("","")") e_list

and print_op ff op =
  fprintf ff "%a %a" print_longname op.op_name print_params op.op_params
  
and print_exp ff e =
  (if !Misc.full_type_info then fprintf ff "(" else ();
    (match e.e_desc with
      | Evar x -> print_ident ff x
      | Econstvar x -> print_name ff x
      | Econst c -> print_c ff c
      | Efby ((Some c), e) ->
          (print_c ff c; fprintf ff " fby "; print_exp ff e)
      | Efby (None, e) -> (fprintf ff "pre "; print_exp ff e)
      | Ecall (op, args, reset) ->
          fprintf ff "%a %a every %a" print_op op print_args args print_ident x
      | Ewhen (e, c, n) ->
          fprintf ff "@[(%a when %a(%a))@]"
            print_exp e print_longname c print_ident n
      | Eifthenelse (e1, e2, e3) ->
          fprintf ff "@[if %a@ then %a@ else @]"
            print_exp e1 print_exp e2 print_exp e3
      | Emerge (x, tag_e_list) ->
          fprintf ff "@[<hov2>merge %a@ @[%a@]@]"
            print_ident x print_tag_e_list tag_e_list
      | Etuple e_list -> (*TODO*)
          (fprintf ff "@[(";
            print_list ff print_exp "," e_list;
            fprintf ff ")@]")
      | Efield (e, field) ->
          (print_exp ff e; fprintf ff "."; print_longname ff field)
      | Estruct f_e_list ->
          (fprintf ff "@[<v 1>{";
            print_list ff
              (fun ff (field, e) ->
                    (print_longname ff field; fprintf ff " = "; print_exp ff e))
              ";" f_e_list;
            fprintf ff "}@]")
      | (*Array operators*) Earray e_list ->
          (fprintf ff "@[[";
            print_list ff print_exp ";" e_list;
            fprintf ff "]@]")
      | Erepeat (n, e) -> (print_exp ff e; fprintf ff "^"; print_size_exp ff n)
      | Eselect (idx, e) ->
          (print_exp ff e;
            fprintf ff "[";
            print_list ff print_size_exp "][" idx;
            fprintf ff "]")
      | Eselect_dyn (idx, _, e1, e2) ->
          (fprintf ff "@[";
            print_exp ff e1;
            fprintf ff "[";
            print_list ff print_exp "][" idx;
            fprintf ff "] default ";
            print_exp ff e2;
            fprintf ff "@]")
      | Eupdate (idx, e1, e2) ->
          (fprintf ff "@[";
            print_exp ff e1;
            fprintf ff " with [";
            print_list ff print_size_exp "][" idx;
            fprintf ff "] = ";
            print_exp ff e2;
            fprintf ff "@]")
      | Eselect_slice (idx1, idx2, e) ->
          (print_exp ff e;
            fprintf ff "[";
            print_size_exp ff idx1;
            fprintf ff "..";
            print_size_exp ff idx2;
            fprintf ff "]")
      | Econcat (e1, e2) ->
          (print_exp ff e1; fprintf ff " @@ "; print_exp ff e2)
      | Eiterator (it, f, params, n, e_list, reset) ->
          (fprintf ff "(";
            fprintf ff "%s" (iterator_to_string it);
            fprintf ff " ";
            (match params with
              | [] -> print_longname ff f
              | l ->
                  (fprintf ff "(";
                    print_longname ff f;
                    print_call_params ff params;
                    fprintf ff ")"));
            fprintf ff " <<";
            print_size_exp ff n;
            fprintf ff ">>) (@[";
            print_list ff print_exp "," e_list;
            fprintf ff ")@]";
            (match reset with
              | None -> ()
              | Some r -> fprintf ff " every %s" (name r)))
      | Efield_update (f, e1, e2) ->
          (fprintf ff "@[";
            print_exp ff e1;
            fprintf ff " with .";
            print_longname ff f;
            fprintf ff " = ";
            print_exp ff e2;
            fprintf ff "@]"));
    if !Misc.full_type_info
    then
      (fprintf ff " : %a)" print_type e.e_ty;
        if e.e_loc = no_location then fprintf ff " (no loc)" else ())
    else ())

and print_tag_e_list ff tag_e_list =
  print_list ff
    (fun ff (tag, e) ->
          (fprintf ff "@[(";
            print_longname ff tag;
            fprintf ff " -> ";
            print_exp ff e;
            fprintf ff ")@]@,"))
    "" tag_e_list

let print_eq ff { eq_lhs = p; eq_rhs = e } = (*     (\* DEBUG *\) *)
  (*     fprintf ff " : "; *) (*     print_ck ff e.e_ck; *)
  (*     (\* END DEBUG *\) *)
  (fprintf ff "@[<hov 2>";
    print_pat ff p;
    fprintf ff " =@ ";
    print_exp ff e;
    if !Misc.full_type_info
    then (fprintf ff "@ at "; print_ck ff e.e_ck)
    else ();
    fprintf ff ";@]")

let print_eqs ff l =
  (fprintf ff "@[<v>"; print_list ff print_eq "" l; fprintf ff "@]")

let print_open_module ff name =
  (fprintf ff "@[open "; print_name ff name; fprintf ff "@.@]")

let print_type_def ff { t_name = name; t_desc = tdesc } =
  match tdesc with
  | Type_abs -> fprintf ff "@[type %s@\n@]" name
  | Type_enum tag_name_list ->
      (fprintf ff "@[type %s = " name;
        print_list ff print_name "|" tag_name_list;
        fprintf ff "@\n@]")
  | Type_struct f_ty_list ->
      (fprintf ff "@[type %s = " name;
        fprintf ff "@[<v 1>{";
        print_list ff
          (fun ff (field, ty) ->
                (print_name ff field; fprintf ff ": "; print_type ff ty))
          ";" f_ty_list;
        fprintf ff "}@]@\n@]")

let print_contract ff
    {
      c_local = l;
      c_eq = eqs;
      c_assume = e_a;
      c_enforce = e_g;
      c_controllables = cl
    } =
  (if l <> []
    then
      (fprintf ff "contract\n";
        fprintf ff "@[<hov 4>var ";
        print_list ff print_vd ";" l;
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
    print_list ff print_vd ";" cl;
    fprintf ff ")")

let print_node_params ff =
  function
  | [] -> ()
  | l -> (fprintf ff "<<"; print_list ff print_name "," l; fprintf ff ">>")

let print_node ff
    {
      n_name = n;
      n_input = ni;
      n_output = no;
      n_contract = contract;
      n_local = nl;
      n_equs = ne;
      n_params = params
    } =
  (fprintf ff "@[<v 2>node %s" n;
    print_node_params ff params;
    fprintf ff "(@[";
    print_list ff print_vd ";" ni;
    fprintf ff "@]) returns (@[";
    print_list ff print_vd ";" no;
    fprintf ff "@])@,";
    optunit (print_contract ff) contract;
    if nl <> []
    then
      (fprintf ff "@[<hov 2>var ";
        print_list ff print_vd ";" nl;
        fprintf ff ";@]@,")
    else ();
    fprintf ff "@[<v 2>let @,";
    print_eqs ff ne;
    fprintf ff "@]@;";
    fprintf ff "tel";
    fprintf ff "@.@]")

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
