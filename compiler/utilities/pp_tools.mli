(**************************************************************************)
(*                                                                        *)
(*  Lucid Synchrone V4                                                    *)
(*  Copyright (C) 2008 Marc Pouzet                                        *)
(*  Organization : LRI, University of Paris-Sud, Orsay                    *)
(*                                                                        *)
(**************************************************************************)
(** Useful stuff for printing *)


(** {2 list couple and option generic functions} *)
(** Most of theses functions export breaks or breaking spaces
  to the calling printer. *)

(** Print the list [x1...xn] as [lp x1 sep \@, x2 ... sep \@, xn rp]
    and nothing if the list is empty,
    no space is added, but a break right after every [sep]. *)
val print_list :
  (Format.formatter -> 'a -> unit) ->
  string -> string -> string -> Format.formatter -> 'a list -> unit

(** Prints the list [x1...xn] : [lp x1 sep \@  x2 ... sep \@  xn rp]
    and nothing if the list is empty
    a breaking space is added after every [sep]. *)
val print_list_r :
  (Format.formatter -> 'a -> unit) ->
  string -> string -> string -> Format.formatter -> 'a list -> unit

(** Print the list [x1...xn] : [lp x1 \@  sep x2 ... \@  sep xn rp]
    and nothing if the list is empty
    a breaking space is added before every [sep]. *)
val print_list_l :
  (Format.formatter -> 'a -> unit) ->
  string -> string -> string -> Format.formatter -> 'a list -> unit

(** Print the couple [(c1,c2)] as [lp c1 sep \@, c2 rp]
    no space is added, but a break right after [sep]. *)
val print_couple :
  (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'b -> unit) ->
  string -> string -> string -> Format.formatter -> 'a * 'b -> unit

(** Print something only in the case of [Some] *)
val print_opt : ('a -> 'b -> unit) -> 'a -> 'b option -> unit

(** Print [sep][s] only when [Some(s)]. *)
val print_opt2 :
  (Format.formatter -> 'a -> unit) ->
  string -> Format.formatter -> 'a option -> unit


(** {2 Common and usual syntax} *)
(** Theses functions are not exporting breaks
    and they assume the same from the print functions passed as arguments *)

(** Print a record as [{field1;\@ field2;\@ ...}] with an hv<2> box *)
val print_record :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit

val print_type_params : Format.formatter -> string list -> unit
