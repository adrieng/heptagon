
(** This modules manages unique identifiers,
  [fresh] generates an identifier from a name
  [name] returns a unique name from an identifier. *)


(** The (abstract) type of identifiers*)
type ident

(** Type to be used for local variables *)
type var_ident = ident

(** Comparision on idents with the same properties as [Pervasives.compare] *)
val ident_compare : ident -> ident -> int

(** Get the source name from an identifier*)
val sourcename : ident -> string
(** Get the full name of an identifier (it is guaranteed to be unique) *)
val name : ident -> string
(** [set_sourcename id v] returns id with its source name changed to v. *)
val set_sourcename : ident -> string -> ident

(** [fresh n] returns a fresh identifier with source name n *)
val fresh : string -> ident
(** [ident_of_name n] returns an identifier corresponding
  to a _source_ variable (do not use it for generated variables). *)
val ident_of_name : string -> ident
(** Resets the sets that makes sure that idents are mapped to unique
    identifiers. Should be called when scoping a new function. *)
val new_function : unit -> unit

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
