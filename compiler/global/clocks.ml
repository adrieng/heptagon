(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Names
open Idents
open Types


type ct =
  | Ck of ck
  | Cprod of ct list

and ck =
  | Cbase
  | Cvar of link ref
  | Con of ck * constructor_name * var_ident

and link =
  | Cindex of int
  | Clink of ck


exception Unify

let invalid_clock = Cprod []


let index = ref 0

let gen_index () = (incr index; !index)

(** returns a new clock variable *)
let fresh_clock () = Cvar { contents = Cindex (gen_index ()); }

(** returns the canonic (short) representant of a [ck]
    and update it to this value. *)
let rec ck_repr ck = match ck with
  | Cbase | Con _ | Cvar { contents = Cindex _ } -> ck
  | Cvar (({ contents = Clink ck } as link)) ->
      let ck = ck_repr ck in (link.contents <- Clink ck; ck)


(** verifies that index is fresh in ck. *)
let rec occur_check index ck =
  let ck = ck_repr ck in
  match ck with
    | Cbase -> ()
    | Cvar { contents = Cindex n } when index <> n -> ()
    | Con (ck, _, _) -> occur_check index ck
    | _ -> raise Unify

(** unify ck *)
let rec unify_ck ck1 ck2 =
  let ck1 = ck_repr ck1 in
  let ck2 = ck_repr ck2 in
  if ck1 == ck2
  then ()
  else
    (match (ck1, ck2) with
       | (Cbase, Cbase) -> ()
       | (Cvar { contents = Cindex n1 }, Cvar { contents = Cindex n2 }) when
           n1 = n2 -> ()
       | (Cvar (({ contents = Cindex n1 } as v)), _) ->
           (occur_check n1 ck2; v.contents <- Clink ck2)
       | (_, Cvar (({ contents = Cindex n2 } as v))) ->
           (occur_check n2 ck1; v.contents <- Clink ck1)
       | (Con (ck1, c1, n1), Con (ck2, c2, n2)) when (c1 = c2) & (n1 = n2) ->
           unify_ck ck1 ck2
       | _ -> raise Unify)

(** unify ct *)
let rec unify t1 t2 =
  if t1 == t2 then () else
  match (t1, t2) with
    | (Ck Cbase, Cprod [])
    | (Cprod [], Ck Cbase) -> ()
    | (Ck ck1, Ck ck2) -> unify_ck ck1 ck2
    | (Cprod t1_list, Cprod t2_list) -> unify_list t1_list t2_list
    | _ -> raise Unify

and unify_list t1_list t2_list =
  try List.iter2 unify t1_list t2_list
  with _ -> raise Unify


let rec skeleton ck = function
  | Tprod ty_list ->
      (match ty_list with
        | [] -> Ck ck
        | _ -> Cprod (List.map (skeleton ck) ty_list))
  | Tarray (t, _) -> skeleton ck t
  | Tid _ | Tinvalid -> Ck ck

(* TODO here it implicitely says that the base clock is Cbase
    and that all tuple is on Cbase *)
let ckofct = function | Ck ck -> ck_repr ck | Cprod _ -> Cbase





