(**************************************************************************)
(*                                                                        *)
(*  Lucid Synchrone                                                       *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* $Id: caml_aux.ml,v 1.1.1.1 2005-11-03 15:45:23 pouzet Exp $ *)

(* file caml-aux.ml *)
(* auxiliary functions for caml expressions *)
(* free variables *)

open Misc;;
open Caml;;
open Declarative;;

(* convertions from declarative structures to caml ones *)
(* immediates *)
let caml_of_declarative_immediate = function
  | Dbool b -> if b then Ftrue else Ffalse
  | Dint i -> Fint i
  | Dfloat f -> Ffloat f
  | Dchar c -> Fchar c
  | Dstring s -> Fstring s

(* globals *)
let string_of_global g =
  let pref = g.dqualid.dqual in
  (if (pref <> "") && (pref <> "Lucy_pervasives") then
    g.dqualid.dqual^"."
  else "") ^ g.dqualid.did

(* pat_desc *)
let rec caml_pattern_of_pat_desc = function
  | Dvarpat i -> Fvarpat ("x__"^(string_of_int i))
  | Dconstantpat i -> Fimpat (caml_of_declarative_immediate i)
  | Dtuplepat pl -> Ftuplepat (List.map caml_of_declarative_pattern pl)
  | Dconstruct0pat g -> Fconstruct0pat (string_of_global g)
  | Dconstruct1pat (g,p) -> Fconstruct1pat (string_of_global g,
              caml_of_declarative_pattern p)
  | Drecordpat gpl -> Frecordpat (List.map
            (fun (x,y) ->
              (string_of_global x,
               caml_of_declarative_pattern y))
            gpl)
(* patterns *)
and caml_of_declarative_pattern p = caml_pattern_of_pat_desc p.dp_desc
(* ---- end of convertions *)

let rec flat_exp_of_pattern = function
  | Fpunit -> Fim Funit
  | Fimpat i -> Fim i
  | Fvarpat v -> Fvar { cvar_name=v; cvar_imported=false }
  | Fconstruct0pat c -> Fconstruct0 c
  | Fconstruct1pat (c,p) -> Fconstruct1 (c, flat_exp_of_pattern p)
  | Ftuplepat pl -> Ftuple (List.map flat_exp_of_pattern pl)
  | Frecordpat cpl ->
      Frecord (List.map (fun (x,y) -> (x,flat_exp_of_pattern y)) cpl)

(* small functions manipulating lists *)
let union x1 x2 =
  let rec rec_union l = function
      [] -> l
    | h::t -> if List.mem h l then (rec_union l t) else (rec_union (h::l) t)
  in
  rec_union x1 x2

let subtract x1 x2 =
  let rec sub l = function
      [] -> l
    | h::t -> if List.mem h x2 then (sub l t) else (sub (h::l) t)
  in
  sub [] x1

let flat l =
  let rec f ac = function
      [] -> ac
    | t::q -> f (ac@t) q
  in
  f [] l

let intersect x1 x2 =
  let rec inter l = function
      [] -> l
    | h::t -> if List.mem h x1 then (inter (h::l) t) else (inter l t)
  in
  inter [] x2

(* make a variable *)
let make_var n = Fvar {cvar_name = n;cvar_imported = false}
and make_imported_var n b = Fvar {cvar_name = n;cvar_imported = b}

let nil_ident = "Lucy__nil"
let state_ident = "Lucy__state"

(* makes a conditional *)
let ifthenelse(c,e1,e2) =
  match c with
    Fim(Ftrue) -> e1
  | Fim(Ffalse) -> e2
  | _ -> Fifthenelse(c,e1,e2)

(* makes a list of conditionnals *)
let ifseq l =
  let rec ifs l =
      let (c,e)::t = l in
      if t = [] then
  e
      else
  ifthenelse (c, e, ifs t)
  in
  ifs l
















