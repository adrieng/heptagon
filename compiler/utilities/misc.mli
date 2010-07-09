(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)


(* Version and date of compilation *)
val version : string
val date : string

(* List of modules initially opened *)
val default_used_modules : string list ref

(* Void the list of modules initially opened *)
val set_no_pervasives : unit -> unit

(* Path list to libraries *)
val load_path : string list ref

(* Set path to standard library *)
val set_stdlib : string -> unit

(* Add path to libraries *)
val add_include : string -> unit

(* Print the path to standard library *)
val locate_stdlib : unit -> unit

(* Print the compiler version and its compilation date *)
val show_version : unit -> unit

(* Verbose option *)
val verbose : bool ref

(* Print types option *)
val print_types : bool ref

(* Nodes to check at run-time *)
val assert_nodes : string list ref

(* Add node (name) to the list of nodes to be checked. *)
val add_assert : string -> unit

(* Simulation mode *)
val simulation : bool ref
(* Simulated node *)
val simulation_node : string option ref
(* Set the simulation mode on *)
val set_simulation_node : string -> unit

(* List of target languages *)
val target_languages : string list ref
(* Add target language to the list *)
val add_target_language : string -> unit

(* Optional path for generated files (C or Java) *)
val target_path : string option ref
(* Set the optional target path *)
val set_target_path : string -> unit

(* Print full type information when pretty-printing MiniLS code. *)
val full_type_info : bool ref

(* Boolean transformation of enumerated types *)
val boolean : bool ref

(* Deadcode removal *)
val deadcode : bool ref

(* Initialization analysis (enabled by default) *)
val init : bool ref

(* Common sub-expression elimination *)
val cse : bool ref

(* Automata minimization *)
val tomato : bool ref

(* Z/3Z back-end mode *)
val set_sigali : unit -> unit

(* Intermediate-equations removal *)
val intermediate : bool ref

(* Nodes to be inlined *)
val nodes_to_inline : string list ref

(* Nodes which dependency graphics will be serialized to .dot file. *)
val nodes_to_display : string list ref

(* Node to flatten *)
val node_to_flatten : string option ref

(* Disable the memory allocation phase*)
val no_mem_alloc : bool ref

(* Whether to use the interference aware scheduler*)
val use_interf_scheduler : bool ref

(* Use the new encoding of resets using reset_mem. *)
val use_new_reset_encoding : bool ref

(* Misc. functions *)
val optional : ('a -> 'b) -> 'a option -> 'b option
(** Optional with accumulator *)
val optional_wacc : ('a -> 'b -> 'c*'a) -> 'a -> 'b option -> ('c option * 'a)
val optunit : ('a -> unit) -> 'a option -> unit
val split_string : string -> char -> string list

(* Printing header informations (compiler version, generation date...) *)
(* [print_header_info ff cbeg cend] prints header info, where [ff] is
   the formatter used, [cbeg] and [cend] the string of begin and end
   of commentaries in the target language *)
val print_header_info : Format.formatter -> string -> string -> unit

(* Error during the whole process *)
exception Error

(* Generation of unique names. Mandatory call of reset_symbol between
   set_min_symbol and gen_symbol *)
(*val set_min_symbol : int -> unit*)
val gen_symbol : unit -> string
val reset_symbol : unit -> unit

(** [unique l] returns the [l] list without duplicates. O([length l]). *)
val unique : 'a list -> 'a list

(** [incomplete_map f l] applies f to all the elements of
  l except the last element. *)
val incomplete_map : ('a -> 'a) -> 'a list -> 'a list

(** [last_element l] returns the last element of the list l.*)
val last_element : 'a list -> 'a

(** [split_last l] returns the list l without its last element
    and the last element of the list .*)
val split_last : 'a list -> ('a list * 'a)

(** [remove x l] removes all occurrences of x from list l.*)
val remove : 'a -> 'a list -> 'a list

(** [is_empty l] returns whether the list l is empty.*)
val is_empty : 'a list -> bool

(** [repeat_list v n] returns a list with n times the value v. *)
val repeat_list : 'a -> int -> 'a list

(** Same as List.mem_assoc but using the value instead of the key. *)
val memd_assoc : 'b -> ('a * 'b) list -> bool

(** Same as List.assoc but searching for a data and returning the key. *)
val assocd: 'b -> ('a * 'b) list -> 'a


(** Ast iterators *)
exception Fallback


(** Mapfold *)
val mapfold: ('a -> 'b -> 'c * 'a) -> 'a -> 'b list -> 'c list * 'a

(** Mapi *)
val mapi: (int -> 'a -> 'b) -> 'a list -> 'b list
val mapi2: (int -> 'a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
val mapi3: (int -> 'a -> 'b -> 'c -> 'd) ->
  'a list -> 'b list -> 'c list -> 'd list

