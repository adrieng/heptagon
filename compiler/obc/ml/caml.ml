(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)


(** Sequential caml code. *)

open Misc
open Names
open Idents
open Location

type caml_code =
    { c_types: (string, type_definition) Hashtbl.t;
      c_defs: (string * cexp) list;
    }

and immediate =
    Cbool of bool
  | Cint of int
  | Cfloat of float
  | Cchar of char
  | Cstring of string
  | Cvoid

and cexp =
    Cconstant of immediate
  | Cglobal of qualified_ident
  | Cvar of string
  | Cconstruct of qualified_ident * cexp list
  | Capply of cexp * cexp list
  | Cfun of pattern list * cexp
  | Cletin of is_rec * (pattern * cexp) list * cexp
  | Cifthenelse of cexp * cexp * cexp
  | Cifthen of cexp * cexp
  | Cmatch of cexp * (pattern * cexp) list
  | Ctuple of cexp list
  | Crecord of (qualified_ident * cexp) list
  | Crecord_access of cexp * qualified_ident
  | Cseq of cexp list
  | Cderef of cexp
  | Cref of cexp
  | Cset of string * cexp
  | Clabelset of string * string * cexp
  | Cmagic of cexp

and is_rec = bool

and pattern =
    Cconstantpat of immediate
  | Cvarpat of string
  | Cconstructpat of qualified_ident * pattern list
  | Ctuplepat of pattern list
  | Crecordpat of (qualified_ident * pattern) list
  | Corpat of pattern * pattern
  | Caliaspat of pattern * string
  | Cwildpat

let cvoidpat = Cconstantpat(Cvoid)
let cvoid = Cconstant(Cvoid)
let crefvoid = Cref(cvoid)
let cfalse = Cconstant(Cbool(false))
let ctrue = Cconstant(Cbool(true))
let creftrue = Cref(ctrue)
let cdummy = Cmagic (Cconstant (Cvoid))
let cand_op = {qual = pervasives_module;id = "&&"}
let cor_op = {qual = pervasives_module;id = "or"}
let cnot_op = {qual = pervasives_module;id = "not"}
let cand c1 c2 = Capply (Cglobal (cand_op), [c1;c2])
let cor c1 c2 = Capply (Cglobal (cor_op), [c1;c2])
let cnot c = Capply(Cglobal (cnot_op),[c])
let cvoidfun e = Cfun([cvoidpat], e)
let cvoidapply e = Capply(e, [cvoid])
let cfun params e =
  match params, e with
  | params, Cfun(others, e) -> Cfun(params @ others, e)
  | [], _ -> cvoidfun e
  | _ ->  Cfun(params, e)
let capply e l = match l with [] -> cvoidapply e | _ -> Capply(e, l)
let cifthen c e = match c with Cconstant(Cbool(true)) -> e | _ -> Cifthen(c, e)
let cifthenelse c e1 e2 =
  match c with
  | Cconstant(Cbool(true)) -> e1
  | Cconstant(Cbool(false)) -> e2
  | _ -> Cifthenelse(c, e1, e2)
let cseq e1 e2 =
  match e1, e2 with
  | Cconstant(Cvoid), _ -> e2
  | _, Cconstant(Cvoid) -> e1
  | e1, Cseq l2 -> Cseq(e1 :: l2)
  | Cseq(l1), e2 -> Cseq (l1 @ [e2])
  | _ -> Cseq[e1;e2]

