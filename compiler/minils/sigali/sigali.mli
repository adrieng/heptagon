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

(* $Id: sigali.mli 2324 2010-12-05 10:22:36Z delaval $ *)

(* Sigali representation and output *)

type name = string

type var = name

type const = Cfalse | Cabsent | Ctrue | Cint of int

type exp =
  | Sconst of const
  | Svar of name
  | Swhen of exp * exp    (* e1 when e2 *)
  | Sdefault of exp * exp (* e1 default e2 *)
  | Sequal of exp * exp   (* e1 = e2 *)
  | Ssquare of exp        (* e^2 *)
  | Snot of exp           (* not e *)
  | Sand of exp * exp     (* e1 and e2 *)
  | Sor of exp * exp      (* e1 or e2 *)
  | Sprim of name * exp list (* f(e1,...,en) *)
  | Slist of exp list     (* [e1,...,en] *)
  | Splus of exp * exp    (* e1 + e2 *)
  | Sminus of exp * exp   (* e1 - e2 *)
  | Sprod of exp * exp    (* e1 * e2 *)

type statement = { (* name : definition *)
  stmt_name : name;
  stmt_def : exp;
}

type objective =
  | Security of exp
  | Reachability of exp
  | Attractivity of exp

type processus = {
  proc_dep : name list;
  proc_name : name;
  proc_inputs : var list;
  proc_uncont_inputs : var list;
  proc_outputs : var list;
  proc_controllables : var list;
  proc_states : var list;
  proc_init : const list;
  proc_constraints : exp list;
  proc_body : statement list;
  proc_objectives : objective list;
}

type program = processus list

val concat : exp -> exp -> exp

val evolutions : string

val initialisations : string

val constraints : string

val extend : name -> exp -> statement

val subst : exp -> exp -> exp -> exp

val l_subst : exp -> exp -> exp -> exp

val evolution : exp -> exp

val initial : exp -> exp

val pconstraint : exp -> exp

val ifthenelse : exp -> exp -> exp -> exp

val ( &~ ) : exp -> exp -> exp

val ( |~ ) : exp -> exp -> exp

val ( ~~ ) : exp -> exp

val ( =>~ ) : exp -> exp -> exp

val a_const : exp -> exp

val a_var : exp -> exp -> exp -> exp -> exp

val a_part : exp -> exp -> exp -> exp -> exp

val a_inf : exp -> exp -> exp

val a_sup : exp -> exp -> exp

val a_iminv : exp -> exp -> exp

module Printer :
  sig
    val print : string -> processus list -> unit
  end
