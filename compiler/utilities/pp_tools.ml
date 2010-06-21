(**************************************************************************)
(*                                                                        *)
(*  Lucid Synchrone V4                                                    *)
(*  Copyright (C) 2008 Marc Pouzet                                        *)
(*  Organization : LRI, University of Paris-Sud, Orsay                    *)
(*                                                                        *)
(**************************************************************************)
(** Useful stuff for printing *)


open Format

(** {2 list couple and option generic functions} *)
(** Most of theses functions export breaks or breaking spaces
  to the calling printer. *)
  
(** Print the list [x1...xn] as [lp x1 sep \@, x2 ... sep \@, xn rp]
    and nothing if the list is empty,
    no space is added, but a break right after every [sep]. *)
let rec print_list print lp sep rp ff = function
  | [] -> ()
  | x::l ->
    fprintf ff "%s%a" lp print x;
    List.iter (fprintf ff "%s@,%a" sep print) l;
    fprintf ff "%s" rp

(** Prints the list [x1...xn] : [lp x1 sep \@  x2 ... sep \@  xn rp]
    and nothing if the list is empty
    a breaking space is added after every [sep]. *)
let rec print_list_r print lp sep rp ff = function
  | [] -> ()
  | x :: l ->
      fprintf ff "%s%a" lp print x;
      List.iter (fprintf ff "%s@ %a" sep print) l;
      fprintf ff "%s" rp 

(** Print the list [x1...xn] : [lp x1 \@  sep x2 ... \@  sep xn rp]
    and nothing if the list is empty
    a breaking space is added before every [sep]. *)
let rec print_list_l print lp sep rp ff = function
  | [] -> ()
  | x :: l ->
      fprintf ff "%s%a" lp print x;
      List.iter (fprintf ff "@ %s%a" sep print) l;
      fprintf ff "%s" rp 

(** Print the couple [(c1,c2)] as [lp c1 sep \@, c2 rp]
    no space is added, but a break right after [sep]. *)
let print_couple print1 print2 lp sep rp ff (c1, c2) =
  fprintf ff "%s%a%s@,%a%s" lp print1 c1 sep print2 c2 rp 

(** Print something only in the case of [Some] *)
let print_opt print ff = function
  | None -> ()
  | Some(s) -> print ff s

(** Print [sep][s] only when [Some(s)]. *)
let print_opt2 print sep ff = function
  | None -> ()
  | Some(s) -> fprintf ff "%s%a" sep print s

(** {2 Common and usual syntax} *)
(** Theses functions are not exporting breaks
    and they assume the same from the print functions passed as arguments *)

(** Print a record as [{field1;\@ field2;\@ ...}] with an hv<2> box
    @param print_field is the print function for a field
    @param record is the list of fields. *)
let print_record print_field ff record =
  fprintf ff "@[<hv2>%a@]" (print_list_r print_field "{ "";"" }") record


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
