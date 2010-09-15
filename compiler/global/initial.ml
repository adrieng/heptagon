(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* initialization of the typing environment *)

open Names
open Types

let tglobal = []
let cglobal = []

let pbool = { qual = "Pervasives"; name = "bool" }
let ptrue = { qual = "Pervasives"; name = "true" }
let pfalse = { qual = "Pervasives"; name = "false" }
let por = { qual = "Pervasives"; name = "or" }
let pint = { qual = "Pervasives"; name = "int" }
let pfloat = { qual = "Pervasives"; name = "float" }

let mk_pervasives s = { qual = "Pervasives"; name = s }

let mk_static_int_op op args =
  mk_static_exp ~ty:(Tid pint) (Sop (op,args))

let mk_static_int i =
  mk_static_exp ~ty:(Tid pint) (Sint i)

let mk_static_bool b =
  mk_static_exp ~ty:(Tid pbool) (Sbool b)



(* build the initial environment *)
let initialize modname =
  Modules.initialize modname;
  List.iter (fun (f, ty) -> Modules.add_type f ty) tglobal;
  List.iter (fun (f, ty) -> Modules.add_constrs f ty) cglobal
