(** The (abstract) type of identifiers*)
type ident 

(** Get the source name from an identifier*)
val sourcename : ident -> string
(** Get the full name of an identifier (it is
    guaranteed to be unique)*)
val name : ident -> string
(** [set_sourcename id v] returns id with its
    source name changed to v. *)
val set_sourcename : ident -> string -> ident

(** [fresh n] returns a fresh identifier with source name n *)
val fresh : string -> ident
(** [ident_of_var n] returns an identifier corresponding
    to a _source_ variable (do not use it for generated variables). *)
val ident_of_var : string -> ident

(** Maps taking an identifier as a key. *)
module Env :
  sig
    include (Map.S with type key = ident)

    val append : 'a t -> 'a t -> 'a t
    val union : 'a t -> 'a t -> 'a t
    val diff : 'a t -> 'b t -> 'a t
    val partition : (key -> bool) -> 'a t -> 'a t * 'a t
  end

(** A set of identifiers. *)
module IdentSet :
  sig
    include (Set.S with type elt = ident)
    val fprint_t : Format.formatter -> t -> unit
  end
