(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* Misc. functions *)
val optional : ('a -> 'b) -> 'a option -> 'b option
(** Optional with accumulator *)
val optional_wacc : ('a -> 'b -> 'c*'a) -> 'a -> 'b option -> ('c option * 'a)
val optunit : ('a -> unit) -> 'a option -> unit

(** [split_string s c] splits the string [s] according to the separator
    [c] into a list of string without [c] *)
val split_string : string -> string -> string list

(* Generation of unique names. Mandatory call of reset_symbol between
   set_min_symbol and gen_symbol *)
(*val set_min_symbol : int -> unit*)
val gen_symbol : unit -> string
val reset_symbol : unit -> unit

(** [unique l] returns the [l] list without duplicates. O([length l]). *)
val unique : 'a list -> 'a list

(** [map_butlast f l] applies f to all the elements of
    l except the last element. *)
val map_butlast : ('a -> 'a) -> 'a list -> 'a list

(** [last_element l] returns the last element of the list l.*)
val last_element : 'a list -> 'a

(** [split_last l] returns the list l without its last element
    and the last element of the list .*)
val split_last : 'a list -> ('a list * 'a)

exception List_too_short
(** [split_at n l] splits [l] in two after the [n]th value.
    Raises List_too_short exception if the list is too short. *)
val split_at : int -> 'a list -> 'a list * 'a list

(** [remove x l] removes all occurrences of x from list l.*)
val remove : 'a -> 'a list -> 'a list

(** [is_empty l] returns whether the list l is empty.*)
val is_empty : 'a list -> bool

(** [repeat_list v n] returns a list with n times the value v. *)
val repeat_list : 'a -> int -> 'a list

(** Same as List.mem_assoc but using the value instead of the key. *)
val memd_assoc : 'b -> ('a * 'b) list -> bool

(** Same as List.assoc but searching for a data and returning the key. *)
val assocd : 'b -> ('a * 'b) list -> 'a

(** [list_compare c l1 l2] compares the lists [l1] and [l2] according to
    lexicographical order induced by [c]. *)
val list_compare : ('a -> 'a -> int) -> 'a list -> 'a list -> int

val option_compare : ('a -> 'a -> int) -> 'a option -> 'a option -> int

(** Mapfold *)
val mapfold: ('acc -> 'b -> 'c * 'acc) -> 'acc -> 'b list -> 'c list * 'acc

(** Mapfold, right version. *)
val mapfold_right
  : ('a -> 'acc -> 'acc * 'b) -> 'a list -> 'acc -> 'acc * 'b list

(** Mapi *)
val mapi: (int -> 'a -> 'b) -> 'a list -> 'b list
val mapi2: (int -> 'a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
val mapi3: (int -> 'a -> 'b -> 'c -> 'd) ->
  'a list -> 'b list -> 'c list -> 'd list
val fold_righti : (int -> 'a -> 'b -> 'b) -> 'a list -> 'b -> 'b

(** [iter_couple f l] calls f for all x and y distinct in [l].  *)
val iter_couple : ('a -> 'a -> unit) -> 'a list -> unit
(** [iter_couple_2 f l1 l2] calls f for all x in [l1] and y in [l2].  *)
val iter_couple_2 : ('a -> 'a -> unit) -> 'a list -> 'a list -> unit

(** Functions to decompose a list into a tuple *)
val assert_empty : 'a list -> unit
val assert_1 : 'a list -> 'a
val assert_1min : 'a list -> 'a * 'a list
val assert_2 : 'a list -> 'a * 'a
val assert_2min : 'a list -> 'a * 'a * 'a list
val assert_3 : 'a list -> 'a * 'a * 'a

(** Print to string *)
val print_pp_to_string : (Format.formatter -> 'a -> unit) -> 'a -> string

(** Replace all non [a-z A-Z 0-9] character of a string by [_] *)
val sanitize_string : string -> string

(** Pipe a value to a function *)
val (|>) : 'a -> ('a -> 'b) -> 'b

(** Return the extension of a filename string *)
val file_extension : string -> string

(** Internal error : Is used when an assertion wrong *)
val internal_error : string -> int -> 'a

(** Unsupported : Is used when something should work but is not currently supported *)
val unsupported : string -> int -> 'a

(** Memoize the result of the function [f]*)
val memoize : ('a -> 'b) -> ('a -> 'b)

(** Memoize the result of the function [f], taht should expect a
   tuple as input and be reflexive (f (x,y) = f (y,x)) *)
val memoize_couple : (('a * 'a) -> 'b) -> (('a * 'a) -> 'b)
