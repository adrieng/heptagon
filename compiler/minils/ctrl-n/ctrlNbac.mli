(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(* Nicolas Berthier, SUMO, INRIA                                       *)
(*                                                                     *)
(* Copyright 2013 ENS, INRIA, UJF                                      *)
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

(* Interface documentation is in `ctrlNbac.ml' only. *)
(** *)

(* -------------------------------------------------------------------------- *)
(** {2 Controllable-Nbac Program Specification} *)

(* -------------------------------------------------------------------------- *)
(** {3 Types} *)

type typname
type label
type typdef
type typdefs
type ntyp = [ `Int | `Real ]
type typ = [ `Bool | `Enum of typname | ntyp ]

(* -------------------------------------------------------------------------- *)
(** {3 Variables} *)

type var
module VMap: Map.S with type key = var
module VSet: Set.S with type elt = var

(* -------------------------------------------------------------------------- *)
(** {3 Expressions} *)

type eqrel = [ `Eq | `Ne ]
type totrel = [ eqrel | `Lt | `Le | `Gt | `Ge ]
type buop = [ `Neg ]
type bnop = [ `Conj | `Disj | `Excl ]
type nuop = [ `Opp ]
type nnop = [ `Add | `Sub | `Mul | `Div ]

type ('t, 'b) cond = [ `Ite of 'b * 't * 't ]

type nexp =
  [
  | `Ref of var
  | `Int of int
  | `Real of float
  | `Nuop of nuop * nexp
  | `Nnop of nnop * nexp * nexp * nexp list
  | ('a, bexp) cond
  ] as 'a
and eexp =
  [
  | `Ref of var
  | `Enum of label
  | ('a, bexp) cond
  ] as 'a
and bexp =
  [
  | `Ref of var
  | `Bool of bool
  | `Buop of buop * bexp
  | `Bnop of bnop * bexp * bexp * bexp list
  | `Bcmp of eqrel * bexp * bexp
  | `Ncmp of totrel * nexp * nexp
  | `Ecmp of eqrel * eexp * eexp
  | `Ein of eexp * label * label list
  | ('a, bexp) cond
  ] as 'a
type exp =
  [
  | `Bexp of bexp
  | `Eexp of eexp
  | `Nexp of nexp
  ]

(* type pbexp = [ exp | bexp ] *)
(* type peexp = [ exp | eexp ] *)
(* type pnexp = [ exp | nexp ] *)

(* -------------------------------------------------------------------------- *)
(** {3 Nodes & Programs} *)

type rank = int
type var_spec =
  | NBstate of exp
  | NBinput
  | NBcontr of rank
  | NBlocal of exp
type var_decl = typ * var_spec
type decls = var_decl VMap.t
type process =
    {
      cn_name: Names.name;
      cn_decls: decls;
      cn_init: bexp;
      cn_assertion: bexp;
      cn_invariance: bexp option;
      cn_reachability: bexp option;
    }
type prog =
    {
      cnp_name: Names.name;
      cnp_typs: typdefs;
      cnp_procs: process list;
    }

(* -------------------------------------------------------------------------- *)
(** {2 Utilities} *)

val mk_var: Names.name -> var
val (^~): string -> var -> var

(* -------------------------------------------------------------------------- *)
(** {3 Building and declaring enumerations} *)

val empty_typdefs: typdefs
val declare_typ: typname -> typdef -> typdefs -> typdefs
val mk_typname: Names.name -> typname
val mk_label: Names.name -> label
val mk_etyp: label list -> typdef

(* -------------------------------------------------------------------------- *)
(** {3 Building expressions} *)

(** The functions bellow are helpers for building expressions.

    Non-primed functions are given polymorphic expressions ({!exp}) and raise
    {!TypeError} exceptions when actual types mismatch; primed versions do not, as
    they take arguments of type {!bexp}, {!nexp} or {!eexp} directly. *)

val mk_bref' : var -> bexp
val mk_bcst' : bool -> bexp
val mk_neg' : bexp -> bexp
val mk_and' : bexp -> bexp -> bexp
val mk_or' : bexp -> bexp -> bexp
val mk_xor' : bexp -> bexp -> bexp
val mk_conj' : bexp -> bexp list -> bexp
val mk_disj' : bexp -> bexp list -> bexp
val mk_excl' : bexp -> bexp list -> bexp
val mk_ein' : eexp -> label -> label list -> bexp
val mk_beq' : bexp -> bexp -> bexp
val mk_eeq' : eexp -> eexp -> bexp
val mk_neq' : nexp -> nexp -> bexp
val mk_bne' : bexp -> bexp -> bexp
val mk_ene' : eexp -> eexp -> bexp
val mk_nne' : nexp -> nexp -> bexp
val mk_lt' : nexp -> nexp -> bexp
val mk_le' : nexp -> nexp -> bexp
val mk_gt' : nexp -> nexp -> bexp
val mk_ge' : nexp -> nexp -> bexp

val mk_eref' : var -> eexp
val mk_ecst' : label -> eexp

val mk_nref' : var -> nexp
val mk_nicst' : int -> nexp
val mk_nrcst' : float -> nexp
val mk_add' : nexp -> nexp -> nexp list -> nexp
val mk_sub' : nexp -> nexp -> nexp list -> nexp
val mk_mul' : nexp -> nexp -> nexp list -> nexp
val mk_div' : nexp -> nexp -> nexp list -> nexp

val mk_cond' : bexp -> ([> `Ite of bexp * 'a * 'a ] as 'a) -> 'a -> 'a
val mk_bcond' : bexp -> bexp -> bexp -> bexp

(* --- *)

exception TypeError of string

val as_bexp: exp -> bexp
val as_eexp: exp -> eexp
val as_nexp: exp -> nexp

type bexp' = [ `Bexp of bexp ]
and eexp' = [ `Eexp of eexp ]
and nexp' = [ `Nexp of nexp ]

val mk_bref : var -> [> bexp' ]
val mk_bcst : bool -> [> bexp' ]
val mk_neg : exp -> [> bexp' ]
val mk_and : exp -> exp -> [> bexp' ]
val mk_or : exp -> exp -> [> bexp' ]
val mk_xor : exp -> exp -> [> bexp' ]
val mk_conj : exp -> exp list -> [> bexp' ]
val mk_disj : exp -> exp list -> [> bexp' ]
val mk_excl : exp -> exp list -> [> bexp' ]
val mk_ein : exp -> label -> label list -> [> bexp' ]
val mk_eq : exp -> exp -> [> bexp' ]
val mk_ne : exp -> exp -> [> bexp' ]
val mk_lt : exp -> exp -> [> bexp' ]
val mk_le : exp -> exp -> [> bexp' ]
val mk_gt : exp -> exp -> [> bexp' ]
val mk_ge : exp -> exp -> [> bexp' ]

val mk_eref : var -> [> eexp' ]
val mk_ecst : label -> [> eexp' ]

val mk_nref : var -> [> nexp' ]
val mk_nicst : int -> [> nexp' ]
val mk_nrcst : float -> [> nexp' ]
val mk_add : exp -> exp -> exp list -> [> nexp' ]
val mk_sub : exp -> exp -> exp list -> [> nexp' ]
val mk_mul : exp -> exp -> exp list -> [> nexp' ]
val mk_div : exp -> exp -> exp list -> [> nexp' ]

val mk_cond : exp -> exp -> exp -> exp
val mk_condb : bexp -> exp -> exp -> exp

(* -------------------------------------------------------------------------- *)
(** {3 Gathering process info} *)

type process_infos =
    {
      cni_state_vars: typ VMap.t;
      cni_input_vars: typ VMap.t;
      cni_contr_vars: (typ * rank) VMap.t;
      cni_contr_vars': (var * typ) list;
      cni_local_vars: typ VMap.t;
      cni_local_specs: exp VMap.t;
      cni_trans_specs: exp VMap.t;
    }
val gather_info: process -> process_infos

(* -------------------------------------------------------------------------- *)
(** {3 Pretty-printing} *)

module Printer: sig

  val print_var : Format.formatter -> var -> unit
  val print_typdef : Format.formatter -> typdef -> unit
  val print_typdefs : Format.formatter -> typdefs -> unit
  val print_bexp : Format.formatter -> bexp -> unit
  val print_eexp : Format.formatter -> eexp -> unit
  val print_nexp : Format.formatter -> nexp -> unit
  val print_exp : Format.formatter -> exp -> unit
  val print_proc : Format.formatter -> process -> unit
  val dump: (Names.name -> Format.formatter * (Format.formatter -> unit)) -> prog ->
    unit

end;;

(* -------------------------------------------------------------------------- *)
