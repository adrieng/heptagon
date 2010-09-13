(**************************************************************************)
(*                                                                        *)
(*  Lucid Synchrone V4                                                    *)
(*  Copyright (C) 2008 Marc Pouzet                                        *)
(*  Organization : LRI, University of Paris-Sud, Orsay                    *)
(*                                                                        *)
(**************************************************************************)
(** Useful stuff for printing *)


open Format

let rec print_list print lp sep rp ff = function
  | [] -> ()
  | x::l ->
      fprintf ff "%s%a" lp print x;
      List.iter (fprintf ff "%s@,%a" sep print) l;
      fprintf ff "%s" rp


let rec print_list_r print lp sep rp ff = function
  | [] -> ()
  | x :: l ->
      fprintf ff "%s%a" lp print x;
      List.iter (fprintf ff "%s@ %a" sep print) l;
      fprintf ff "%s" rp


let rec print_list_l print lp sep rp ff = function
  | [] -> ()
  | x :: l ->
      fprintf ff "%s%a" lp print x;
      List.iter (fprintf ff "@ %s%a" sep print) l;
      fprintf ff "%s" rp


let print_couple print1 print2 lp sep rp ff (c1, c2) =
  fprintf ff "%s%a%s@,%a%s" lp print1 c1 sep print2 c2 rp


let print_opt print ff = function
  | None -> ()
  | Some(s) -> print ff s


let print_opt2 print sep ff = function
  | None -> ()
  | Some(s) -> fprintf ff "%s%a" sep print s


let print_record print_field ff record =
  fprintf ff "@[<hv2>%a@]" (print_list_r print_field "{ "";"" }") record


let print_type_params ff pl =
  fprintf ff "@[%a@]"
    (print_list_r (fun ff s -> fprintf ff "'%s" s) "("","") ") pl


let print_set iter print_element ff set =
  fprintf ff "@[{@ ";
  iter (fun e -> fprintf ff "%a@ " print_element e) set;
  fprintf ff "}@]"

let print_map iter print_key print_element ff map =
  fprintf ff "@[<hv 2>[@ ";
  iter (fun k x -> fprintf ff "| %a -> %a@ " print_key k print_element x) map;
  fprintf ff "]@]"
