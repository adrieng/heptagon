(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)

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

(** returns a new clock type corresponding to the data type [ty] *)
let rec fresh_ct ty = match ty with
  | Tprod ty_list ->
      (match ty_list with
        | [] -> Ck (fresh_clock())
        | _ -> Cprod (List.map fresh_ct ty_list))
  | Tarray (t, _) -> fresh_ct t
  | Tid _ | Tinvalid -> Ck (fresh_clock())


(** returns the canonic (short) representant of a [ck]
    and update it to this value. *)
let rec ck_repr ck = match ck with
  | Cbase | Con _
  | Cvar { contents = Cindex _ } -> ck
  | Cvar (({ contents = Clink ck } as link)) ->
      let ck = ck_repr ck in
      link.contents <- Clink ck;
      ck


(** verifies that index is fresh in ck. *)
let rec occur_check index ck =
  let ck = ck_repr ck in
  match ck with
    | Cbase -> ()
    | Cvar { contents = Cindex n } when index <> n -> ()
    | Con (ck, _, _) -> occur_check index ck
    | _ -> raise Unify


(** unify ck *)
and unify_ck ck1 ck2 =
  let ck1 = ck_repr ck1 in
  let ck2 = ck_repr ck2 in
  if ck1 == ck2 then ()
  else
    match (ck1, ck2) with
     | Cbase, Cbase -> ()
     | Cvar { contents = Cindex n1 }, Cvar { contents = Cindex n2 } when n1 = n2 -> ()
     | Con (ck1, c1, n1), Con (ck2, c2, n2) when (c1 = c2) && (n1 = n2) ->
         unify_ck ck1 ck2
     | Cvar ({ contents = Cindex n } as v), ck
     | ck, Cvar ({ contents = Cindex n } as v) ->
          occur_check n ck;
         v.contents <- Clink ck
     | _ -> raise Unify


(** unify ct *)
let rec unify t1 t2 =
  if t1 == t2 then () else
  match (t1, t2) with
    | (Ck (Cbase | Cvar { contents = Cindex _; }), Cprod [])
    | (Cprod [], Ck (Cbase | Cvar { contents = Cindex _; })) -> ()
    | (Ck ck1, Ck ck2) -> unify_ck ck1 ck2
    | (Cprod t1_list, Cprod t2_list) -> unify_list t1_list t2_list
    | _ -> raise Unify

and unify_list t1_list t2_list =
  try List.iter2 unify t1_list t2_list
  with _ -> raise Unify


let rec skeleton ck = function
  | Tprod ty_list ->
      (match ty_list with
        | [_] -> Ck ck
        | l -> Cprod (List.map (skeleton ck) l))
  | Tarray _ | Tid _ | Tinvalid -> Ck ck

let unprod ct =
  let rec f acc ct = match ct with
    | Ck ck -> ck::acc
    | Cprod ct_l -> List.fold_left f acc ct_l
  in
  f [] ct

let prod ck_l = match ck_l with
  | [ck] -> Ck ck
  | _ -> Cprod (List.map (fun ck -> Ck ck) ck_l)

let rec root_ck_of ck = match ck_repr ck with
  | Cbase
  | Cvar { contents = Cindex _ } -> ck
  | Con(ck,_,_) -> root_ck_of ck
  | Cvar { contents = Clink _ } -> Misc.internal_error "Clocks, wrong repr"

let rec last_clock ct = match ct with
  | Ck ck -> ck
  | Cprod l -> last_clock (Misc.last_element l)

(** returns whether [ck1] and [ck2] are leafs of the same clock node :
  E.g. .... on C1(x) and .... on C2(x) are. *)
let same_control ck1 ck2 = match ck_repr ck1, ck_repr ck2 with
  | Cbase, Cbase -> true
  | Con(_,_,x1), Con(_,_,x2) -> x1 = x2
  | Cvar {contents = Cindex i1}, Cvar {contents = Cindex i2} -> i1 = i2
  | _ -> false

(** returns the first clock of a ct. *)
let rec first_ck ct = match ct with
  | Ck ck -> ck
  | Cprod [] -> assert false
  | Cprod (ct::_) -> first_ck ct

let rec list_of_samplers acc ck = match ck with
  | Cbase | Cvar { contents = Cindex _ } -> acc
  | Con(ck, c, x) -> list_of_samplers ((c, x)::acc) ck
  | Cvar { contents = Clink ck } -> list_of_samplers acc ck

let are_disjoint ck1 ck2 =
  let rec disjoint_samplers s_ck1 s_ck2 = match s_ck1, s_ck2 with
    | [], _ -> false
    | _ , [] -> false
    | (c1, x1)::s_ck1, (c2, x2)::s_ck2 ->
        if Idents.ident_compare x1 x2 <> 0 then
          false
        else
          c1 <> c2 || disjoint_samplers s_ck1 s_ck2
  in
  disjoint_samplers (list_of_samplers [] ck1) (list_of_samplers [] ck2)

(* returns whether ck1 is included in ck2. *)
let is_subclock ck1 ck2 =
  let rec sub_samplers s_ck1 s_ck2 = match s_ck1, s_ck2 with
    | _, [] -> true
    | [], _ -> false
    | (c1, x1)::s_ck1, (c2, x2)::s_ck2 ->
      if Idents.ident_compare x1 x2 <> 0 then
        false
      else
        c1 = c2 && sub_samplers s_ck1 s_ck2
  in
  sub_samplers (list_of_samplers [] ck1) (list_of_samplers [] ck2)
