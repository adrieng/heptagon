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

(* Module objects and global environnement management *)


open Compiler_options
open Signature
open Types
open Names

exception Already_defined


(* Warning: Whenever this type is modified,
   interface_format_version in signature.ml should be incremented. *)
(** Object serialized in compiled interfaces. *)
type module_object =
  { m_name    : Names.modul;
    m_values  : node NamesEnv.t;
    m_types   : type_def NamesEnv.t;
    m_consts  : const_def NamesEnv.t;
    m_constrs : name NamesEnv.t;
    m_fields  : name NamesEnv.t;
    m_format_version : string; }

type env = {
    mutable current_mod : modul;           (** Current module name *)
    mutable opened_mod  : modul list;      (** Modules opened and loaded into the env *)
    mutable loaded_mod  : modul list;      (** Modules loaded into the env *)
    mutable values  : node QualEnv.t;      (** Node definitions *)
    mutable types   : type_def QualEnv.t;  (** Type definitions *)
    mutable consts  : const_def QualEnv.t; (** Constants definitions *)
    mutable constrs  : qualname QualEnv.t; (** Constructors mapped to their corresponding type *)
    mutable fields  : qualname QualEnv.t;  (** Fields mapped to their corresponding type *)
    format_version  : string               (** Accepted compiled interface version *)
  }

(** The global environnement *)
let g_env =
  { current_mod = Module "";
    opened_mod  = [];
    loaded_mod = [];
    values  = QualEnv.empty;
    types   = QualEnv.empty;
    constrs = QualEnv.empty;
    fields  = QualEnv.empty;
    consts  = QualEnv.empty;
    format_version = interface_format_version }


let is_loaded m = List.mem m g_env.loaded_mod
let is_opened m = List.mem m g_env.opened_mod


(** Append a module to the global environnment *)
let _append_module mo =
  (* Transforms a module object NamesEnv into its qualified version *)
  let qualify mo_env = (* qualify env keys *)
    NamesEnv.fold
      (fun x v env -> QualEnv.add { qual = mo.m_name; name = x } v env)
      mo_env QualEnv.empty in
  let qualify_all mo_env = (* qualify env keys and values *)
    NamesEnv.fold
      (fun x v env ->
        QualEnv.add {qual= mo.m_name; name= x} {qual= mo.m_name; name= v} env)
      mo_env QualEnv.empty in
  g_env.values <- QualEnv.append (qualify mo.m_values) g_env.values;
  g_env.types <- QualEnv.append (qualify mo.m_types) g_env.types;
  g_env.constrs <- QualEnv.append (qualify_all mo.m_constrs) g_env.constrs;
  g_env.fields <- QualEnv.append (qualify_all mo.m_fields) g_env.fields;
  g_env.consts <- QualEnv.append (qualify mo.m_consts) g_env.consts

(** Load a module into the global environment unless already loaded *)
let _load_module modul =
  if is_loaded modul then ()
  else
    let modname = match modul with
      | Names.Pervasives -> "Pervasives"
      | Names.Module n -> n
      | Names.LocalModule -> Misc.internal_error "modules"
      | Names.QualModule _ -> Misc.unsupported "modules"
    in
    let name = String.uncapitalize_ascii modname in
    try
      let filename = Compiler_utils.findfile (name ^ ".epci") in
      let ic = open_in_bin filename in
      let mo:module_object =
        try input_value ic
        with End_of_file | Failure _ ->
          close_in ic;
          Format.eprintf "Corrupted compiled interface file %s.@\n\
                          Please recompile %s.ept first.@." filename name;
          raise Errors.Error
      in
      if mo.m_format_version <> interface_format_version
      then (
        Format.eprintf "The file %s was compiled with an older version \
                        of the compiler.@\nPlease recompile %s.ept first.@."
                       filename name;
        raise Errors.Error );
      g_env.loaded_mod <- modul::g_env.loaded_mod;
      _append_module mo
    with
      | Compiler_utils.Cannot_find_file(f) ->
          Format.eprintf "Cannot find the compiled interface file %s.@." f;
          raise Errors.Error



(** Opens a module unless already opened
    by loading it into the global environment and setting it as opened *)
let open_module modul =
  if is_opened modul then ()
  else
    _load_module modul;
    g_env.opened_mod <- modul::g_env.opened_mod


(** Initialize the global environment :
    set current module and open default modules *)
let initialize modul =
  g_env.current_mod <- modul;
  g_env.opened_mod <- [];
  g_env.loaded_mod <- [modul];
  List.iter open_module !default_used_modules


let current () = g_env.current_mod
let select modul = g_env.current_mod <- modul


(** {3 Add functions prevent redefinitions} *)

let _check_not_defined env f =
  if QualEnv.mem f env then raise Already_defined

let add_value f v =
  _check_not_defined g_env.values f;
  g_env.values <- QualEnv.add f v g_env.values
let add_type f v =
  _check_not_defined g_env.types f;
  g_env.types <- QualEnv.add f v g_env.types
let add_constrs f v =
  _check_not_defined g_env.constrs f;
  g_env.constrs <- QualEnv.add f v g_env.constrs
let add_field f v =
  _check_not_defined g_env.fields f;
  g_env.fields <- QualEnv.add f v g_env.fields
let add_const f v =
  _check_not_defined g_env.consts f;
  g_env.consts <- QualEnv.add f v g_env.consts

(** Same as add_value but without checking for redefinition *)
let replace_value f v =
  g_env.values <- QualEnv.add f v g_env.values
let replace_type f v =
  g_env.types <- QualEnv.add f v g_env.types
let replace_const f v =
  g_env.consts <- QualEnv.add f v g_env.consts

(** {3 Find functions look in the global environement, nothing more} *)

let find_value x = QualEnv.find x g_env.values
let find_type x = QualEnv.find x g_env.types
let find_constrs x = QualEnv.find x g_env.constrs
let find_field x = QualEnv.find x g_env.fields
let find_const x = QualEnv.find x g_env.consts

(** @return the fields of a record type. *)
let find_struct n =
  match find_type n with
    | Tstruct fields -> fields
    | _ -> raise Not_found

(** {3 Check functions}
    Try to load the needed module and then to find it,
    return true if in the table, return false if it can't find it. *)

(* NB : we can't factorize this functions since g_env is changed by _load... *)
let check_value q =
  _load_module q.qual;
  try let _ = QualEnv.find q g_env.values in true with Not_found -> false
let check_type q =
  _load_module q.qual;
  try let _ = QualEnv.find q g_env.types in true with Not_found -> false
let check_constrs q =
  _load_module q.qual;
  try let _ = QualEnv.find q g_env.constrs in true with Not_found -> false
let check_field q =
  _load_module q.qual;
  try let _ = QualEnv.find q g_env.fields in true with Not_found -> false
let check_const q =
  _load_module q.qual;
  try let _ = QualEnv.find q g_env.consts in true with Not_found -> false


(** {3 Qualify functions}

    [qualify_* name] return the qualified name matching [name] in the global env
    scope (current module :: opened modules).

    @raise Not_found if not in scope *)

let _qualify env name =
  let tries m =
    try
      let _ = QualEnv.find { qual = m; name = name } env in
      true
    with Not_found -> false in
  let m = List.find tries (g_env.current_mod::g_env.opened_mod) in
  { qual = m; name = name }

let qualify_value name = _qualify g_env.values name
let qualify_type name = _qualify g_env.types name
let qualify_constrs name = _qualify g_env.constrs name
let qualify_field name = _qualify g_env.fields name
let qualify_const name = _qualify g_env.consts name


(** @return the name as qualified with the current module
    (should not be used..)*)
let current_qual n = { qual = g_env.current_mod; name = n }


(** {3 Fresh functions return a fresh qualname for the current module} *)

let rec fresh_value pass_name name =
  let fname =
    if !Compiler_options.full_name
    then ("__"^ pass_name ^"_"^ name)
    else name in
  let q = current_qual fname in
  if QualEnv.mem q g_env.values
  then fresh_value pass_name (name ^ Misc.gen_symbol())
  else q

let rec fresh_value_in pass_name name qualifier =
  let fname =
    if !Compiler_options.full_name
    then ("__"^ pass_name ^"_"^ name)
    else name in
  let q = { qual = qualifier; name = fname } in
  if QualEnv.mem q g_env.values
  then fresh_value_in pass_name (name ^ Misc.gen_symbol()) qualifier
  else q

let rec fresh_type pass_name name =
  let fname =
    if !Compiler_options.full_name
    then ("__"^ pass_name ^"_"^ name)
    else name in
  let q = current_qual fname in
  if QualEnv.mem q g_env.types
  then fresh_type pass_name (name ^ Misc.gen_symbol())
  else q

let rec fresh_const pass_name name =
  let fname =
    if !Compiler_options.full_name
    then ("__"^ pass_name ^"_"^ name)
    else name in
  let q = current_qual fname in
  if QualEnv.mem q g_env.consts
  then fresh_const pass_name (name ^ Misc.gen_symbol())
  else q

let rec fresh_constr pass_name name =
  let fname =
    if !Compiler_options.full_name
    then ("__"^ pass_name ^"_"^ name)
    else name in
  let q = current_qual fname in
  if QualEnv.mem q g_env.constrs
  then fresh_constr pass_name (name ^ Misc.gen_symbol())
  else q


exception Undefined_type of qualname

(** @return the unaliased version of a type.

    @raise Undefined_type . *)
let rec unalias_type t = match t with
  | Tid ({ qual = q } as ty_name) ->
    _load_module q;
      (try
        match find_type ty_name with
          | Talias ty -> unalias_type ty
          | _ -> t
      with Not_found -> raise (Undefined_type ty_name))
  | Tarray (ty, n) -> Tarray(unalias_type ty, n)
  | Tprod ty_list -> Tprod (List.map unalias_type ty_list)
  | Tinvalid -> Tinvalid


(** Return the current module as a {!module_object} *)
let current_module () =
  (* Filter and transform a qualified env into the current module object env *)
  let unqualify env = (* unqualify and filter env keys *)
    QualEnv.fold
      (fun x v current ->
        if x.qual = g_env.current_mod
        then NamesEnv.add x.name v current
        else current) env NamesEnv.empty in
  let unqualify_all env = (* unqualify and filter env keys and values *)
    QualEnv.fold
      (fun x v current ->
        if x.qual = g_env.current_mod
        then NamesEnv.add x.name v.name current
        else current) env NamesEnv.empty in
    { m_name = g_env.current_mod;
      m_values = unqualify g_env.values;
      m_types = unqualify g_env.types;
      m_consts = unqualify g_env.consts;
      m_constrs = unqualify_all g_env.constrs;
      m_fields = unqualify_all g_env.fields;
      m_format_version = g_env.format_version }
