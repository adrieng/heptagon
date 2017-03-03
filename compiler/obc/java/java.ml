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

(** [qual] is the package name, [Name] is the class name *)
type class_name = Names.qualname

type obj_ident = Idents.var_ident

(** [Qual] is the enum class name (type), [NAME] is the constructor name *)
type constructor_name = Names.qualname
type const_name = Names.qualname
type method_name = Names.name
type field_name = Names.name
type field_ident = Idents.var_ident
type op_name = Names.qualname
type var_ident = Idents.var_ident

type ty = Tclass of class_name
        | Tgeneric of class_name * ty list
        | Tbool
        | Tint
        | Tlong
        | Tfloat
        | Tarray of ty * exp list
        | Tunit

and classe = { c_protection : protection;
               c_static     : bool;
               c_name       : class_name;
               c_imports     : class_name list;
               c_implements : class_name list;
               c_kind       : class_kind }

and class_kind = Cenum of constructor_name list
               | Cgeneric of class_desc

and class_desc = { cd_fields       : field list;
                   cd_classs       : classe list;
                   cd_constructors : methode list;
                   cd_methodes     : methode list; }

and var_dec = { vd_type  : ty;
                vd_alias : bool;
                vd_ident : var_ident }

and protection = Ppublic | Pprotected | Pprivate | Ppackage

and field = { f_protection : protection;
              f_static     : bool;
              f_final      : bool;
              f_type       : ty;
              f_ident      : field_ident;
              f_value      : exp option }

and methode = { m_protection : protection;
                m_static     : bool;
                m_name       : method_name;
                m_args       : var_dec list;
                m_returns    : ty;
                m_throws     : class_name list;
                m_body       : block; }


and block = { b_locals : var_dec list;
              b_body   : act list; }

and act = Anewvar of var_dec * exp
        | Aassgn of pattern * exp
        | Aexp of exp
        | Aswitch of exp * (switch_case * block) list
        | Aif of exp * block
        | Aifelse of exp * block * block
        | Ablock of block
        | Afor of var_dec * exp * exp * block
        | Areturn of exp

and switch_case = Senum of constructor_name | Sexp of exp

and exp = Ethis
        | Efun of op_name * exp list
        | Emethod_call of exp * method_name * exp list
        | Enew of ty * exp list
        | Enew_array of ty * exp list (** [ty] is the array base type *)
        | Evoid (*printed as nothing*)
        | Ecast of ty * exp
        | Svar of const_name
        | Sint of int
        | Sfloat of float
        | Sbool of bool
        | Sconstructor of constructor_name
        | Sstring of string
        | Snull
        | Efield of exp * field_name
        | Eclass of class_name
        | Evar of var_ident
        | Earray_elem of exp * exp list

and pattern = Pfield of pattern * field_name
            | Pclass of class_name
            | Pvar of var_ident
            | Parray_elem of pattern * exp list
            | Pthis of field_ident

type program = classe list


(** [jname_of_name name] translates the string [name] to a valid Java identifier. *)
let jname_of_name name =
  let buf = Buffer.create (String.length name) in
  let convert c =
    match c with
      | 'A'..'Z' | 'a'..'z' | '0'..'9' | '_' ->
          Buffer.add_char buf c
      | '\'' -> Buffer.add_string buf "_prime"
      | _ ->
          Buffer.add_string buf "lex";
          Buffer.add_string buf (string_of_int (Char.code c)) in
  String.iter convert name;
  Buffer.contents buf


let default_value ty = match ty with
  | Tclass _ -> Snull
  | Tgeneric _ -> Snull
  | Tbool -> Sbool true
  | Tint -> Sint 0
  | Tlong -> Sint 0
  | Tfloat -> Sfloat 0.0
  | Tunit -> Evoid
  | Tarray _ -> Enew_array (ty,[])


let java_pervasive_class c = Names.qualname_of_string ("jeptagon.Pervasives."^c)
let java_pervasives_name = Names.qualname_of_string "jeptagon.Pervasives"
let java_pervasives = Eclass java_pervasives_name


let mk_var x = Evar x

let mk_var_dec x is_alias ty =
  { vd_type = ty; vd_alias = is_alias; vd_ident = x }

let mk_block ?(locals=[]) b =
  { b_locals = locals; b_body = b; }


let mk_methode ?(protection=Ppublic) ?(static=false) ?(args=[]) ?(returns=Tunit) ?(throws=[])
               body name =
  { m_protection = protection; m_static = static; m_name = name; m_args = args;
    m_throws = throws; m_returns = returns; m_body = body; }

let mk_classe ?(imports=[]) ?(protection=Ppublic) ?(static=false) ?(fields=[])
              ?(classes=[]) ?(constrs=[]) ?(methodes=[]) ?(implements=[])
              class_name =
  { c_protection = protection; c_static = static; c_name = class_name;
    c_imports = imports; c_implements = implements;
    c_kind = Cgeneric { cd_fields = fields; cd_classs = classes;
                        cd_constructors = constrs; cd_methodes = methodes; } }

let mk_enum ?(protection=Ppublic) ?(static=false) ?(imports=[]) ?(implements=[])
            constructor_names class_name =
  { c_protection = protection; c_static = static; c_name = class_name;
    c_imports = imports; c_implements = implements;
    c_kind = Cenum(constructor_names) }


let mk_field ?(protection = Ppublic) ?(static = false) ?(final = false) ?(value = None) ty ident =
  { f_protection = protection; f_static = static; f_final = final;
    f_type = ty; f_ident = ident; f_value = value }

let vds_to_exps vd_l = List.map (fun { vd_ident = x } -> mk_var x) vd_l

let vds_to_fields ?(protection=Ppublic) vd_l =
  List.map (fun { vd_ident = x; vd_type = t } -> mk_field ~protection:protection t x) vd_l
