(**************************************************************************)
(*                                                                        *)
(*  Lucid Synchrone V4                                                    *)
(*  Copyright (C) 2008 Marc Pouzet                                        *)
(*  Organization : LRI, University of Paris-Sud, Orsay                    *)
(*                                                                        *)
(**************************************************************************)
(* useful stuff for printing *)
(* $Id: pp_tools.ml,v 1.12.4.1 2009-07-12 09:40:19 gerard Exp $ *)

open Format

(** print the list x1...xn : \@\[[lp][x1][sep][x2]...[sep][xn][rp]\]\@
    and nothing if the list is empty *)
let rec print_list print lp sep rp ff = function
  | [] -> ()
  | x::l ->
    fprintf ff "%s%a" lp print x;
    List.iter (fprintf ff "%s@,%a" sep print) l;
    fprintf ff "%s" rp

(** print the list x1...xn : \@\[[lp][x1][sep] [x2]...[sep] [xn][rp]\]\@
    and nothing if the list is empty *)
let rec print_list_r print lp sep rp ff = function
  | [] -> ()
  | x :: l ->
      fprintf ff "%s%a" lp print x;
      List.iter (fprintf ff "%s@ %a" sep print) l;
      fprintf ff "%s" rp 

(** print the list x1...xn : \@\[[lp][x1] [sep][x2]... [sep][xn][rp]\]\@
    and nothing if the list is empty *)
let rec print_list_l print lp sep rp ff = function
  | [] -> ()
  | x :: l ->
      fprintf ff "%s%a" lp print x;
      List.iter (fprintf ff "@ %s%a" sep print) l;
      fprintf ff "%s" rp 
(*
let rec print_list_rb print lp sep rp ff = function
  | [] -> ()
  | x :: l ->
      fprintf ff "@[<2>%s%a" lp print x;
      List.iter (fprintf ff "%s@]@ @[<2>%a" sep print) l;
      fprintf ff "%s@]" rp 

let rec print_list_lb print lp sep rp ff = function
  | [] -> ()
  | x :: l ->
      fprintf ff "@[<2>%s%a@]" lp print x;
      List.iter (fprintf ff "@]@ @[<2>%s%a" sep print) l;
      fprintf ff "%s@]" rp 
*)
let print_couple print1 print2 lp sep rp ff (c1, c2) =
  fprintf ff "%s%a%s@ %a%s" lp print1 c1 sep print2 c2 rp 

let print_couple2 print1 print2 lp sep1 sep2 rp ff (c1, c2) =
  fprintf ff "%s%a%s@ %s%a%s" lp print1 c1 sep1 sep2 print2 c2 rp 

let print_opt print ff = function
  | None -> ()
  | Some(s) -> print ff s

let print_opt_magic print ff = function
  | None -> pp_print_string ff "Obj.magic ()"
  | Some(e) -> print ff e


let print_opt2 print sep ff = function
  | None -> ()
  | Some(s) -> fprintf ff "%s%a" sep print s

let print_record print ff r =
  fprintf ff "@[<hv2>%a@]" (print_list_r print "{ "";"" }") r

let print_type_params ff pl =
  print_list_r (fun ff s -> fprintf ff "'%s" s) "("","") " ff pl


(* Map and Set redefinition to allow pretty printing

module type P = sig
        type t
        val fprint : Format.formatter -> t -> unit
end

module type ELT = sig
        type t
        val compare : t -> t -> int
        val fprint : Format.formatter -> t -> unit
end

module SetMake (Elt : ELT) = struct
        module M = Set.Make(Elt)
        include M
        let fprint ff es =
                Format.fprintf ff "@[<hov>{@ ";
                iter (fun e -> Format.fprintf ff "%a@ " Elt.fprint e) es;
                Format.fprintf ff "}@]";
end

module MapMake (Key : ELT) (Elt : P) = struct
        module M = Map.Make(Key)
        include M
        let fprint prp  eem =
                Format.fprintf prp  "[@[<hv 2>";
                iter (fun k m -> Format.fprintf prp  "@ | %a -> %a" Key.fprint k Elt.fprint m) eem;
                Format.fprintf prp  "@]@ ]";
end
*)
