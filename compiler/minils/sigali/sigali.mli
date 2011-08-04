(****************************************************)
(*                                                  *)
(*  Sigali Library                                  *)
(*                                                  *)
(*  Author : Gwenaël Delaval                        *)
(*  Organization : INRIA Rennes, VerTeCs            *)
(*                                                  *)
(****************************************************)

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

val ( =>~ ) : exp -> exp -> exp

val a_const : exp -> exp

val a_var : exp -> exp -> exp -> exp -> exp

val a_part : exp -> exp -> exp -> exp -> exp

val a_inf : exp -> exp -> exp

val a_sup : exp -> exp -> exp

module Printer :
  sig
    val print : string -> processus list -> unit
  end
