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

let pbool = { qual = Pervasives; name = "bool" }
let tbool = Types.Tid pbool
let ptrue = { qual = Pervasives; name = "true" }
let pfalse = { qual = Pervasives; name = "false" }
let por = { qual = Pervasives; name = "or" }
let pint = { qual = Pervasives; name = "int" }
let tint = Types.Tid pint
let pfloat = { qual = Pervasives; name = "float" }
let tfloat = Types.Tid pfloat
let pstring = { qual = Pervasives; name = "string" }
let tstring = Types.Tid pstring

let pfile = { qual = Module "Iostream"; name = "file" }
let tfile = Types.Tid pfile

let mk_pervasives s = { qual = Pervasives; name = s }

let mk_static_int_op op args =
  mk_static_exp tint (Sop (op,args))

let mk_static_int i =
  mk_static_exp tint (Sint i)

let mk_static_bool b =
  mk_static_exp tbool (Sbool b)

let mk_static_string s =
  mk_static_exp  tstring (Sstring s)


(* build the initial environment *)
let initialize modul =
  Modules.initialize modul;
  List.iter (fun (f, ty) -> Modules.add_type f ty) tglobal;
  List.iter (fun (f, ty) -> Modules.add_constrs f ty) cglobal
