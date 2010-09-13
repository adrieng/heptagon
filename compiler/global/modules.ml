(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* Module objects and global environnement management *)


open Misc
open Signature
open Types
open Names

exception Already_defined


(** Warning: Whenever this type is modified,
    interface_format_version in signature.ml should be incremented. *)
(** Object serialized in compiled interfaces. *)
type module_object =
  { m_name    : string;
    m_values  : node NamesEnv.t;
    m_types   : type_def NamesEnv.t;
    m_consts  : const_def NamesEnv.t;
    m_constrs : name NamesEnv.t;
    m_fields  : name NamesEnv.t;
    m_format_version : string; }

type env = {
  (** Current module name *)
  mutable current_mod : module_name;
  (** Modules opened and loaded into the env *)
  mutable opened_mod  : module_name list;
  (** Modules loaded into the env *)
  mutable loaded_mod  : module_name list;
  (** Node definitions *)
  mutable values  : node QualEnv.t;
  (** Type definitions *)
  mutable types   : type_def QualEnv.t;
  (** Constants definitions *)
  mutable consts  : const_def QualEnv.t;
  (** Constructors mapped to their corresponding type *)
  mutable constrs  : qualname QualEnv.t;
  (** Fields mapped to their corresponding type *)
  mutable fields  : qualname QualEnv.t;
  (** Accepted compiled interface version *)
  format_version  : string }

(** The global environnement *)
let g_env =
  { current_mod = "";
    opened_mod  = [];
    loaded_mod = [];
    values  = QualEnv.empty;
    types   = QualEnv.empty;
    constrs  = QualEnv.empty;
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

(** Load a module into the global environnement unless already loaded *)
let _load_module modname =
  if is_loaded modname then ()
  else
    let name = String.uncapitalize modname in
    try
      let filename = Misc.findfile (name ^ ".epci") in
      let ic = open_in_bin filename in
      let mo:module_object =
        try
          input_value ic
        with
          | End_of_file | Failure _ ->
              close_in ic;
              Format.eprintf "Corrupted compiled interface file %s.@\n\
                              Please recompile %s.ept first.@." filename name;
              raise Error in
      if mo.m_format_version <> interface_format_version
      then (
        Format.eprintf "The file %s was compiled with an older version \
                        of the compiler.@\nPlease recompile %s.ept first.@."
                       filename name;
        raise Error );
      _append_module mo
    with
      | Misc.Cannot_find_file(f) ->
          Format.eprintf "Cannot find the compiled interface file %s.@." f;
          raise Error



(** Opens a module unless already opened
    by loading it into the global environnement and seting it as opened *)
let open_module modname =
  if is_opened modname then ()
  else
    _load_module modname;
    g_env.opened_mod <- modname::g_env.opened_mod


(** Initialize the global environnement :
    set current module and open default modules *)
let initialize modname =
  g_env.current_mod <- modname;
  g_env.opened_mod <- [];
  g_env.loaded_mod <- [modname];
  List.iter open_module !default_used_modules


(** { 3 Add functions prevent redefinitions } *)

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

(** { 3 Find functions look in the global environnement, nothing more } *)

let _find env x = QualEnv.find x env

let find_value x = _find g_env.values x
let find_type x = _find g_env.types x
let find_constrs x = _find g_env.constrs x
let find_field x = _find g_env.fields x
let find_const x = _find g_env.consts x

(** @return the fields of a record type. *)
let find_struct n =
  match find_type n with
    | Tstruct fields -> fields
    | _ -> raise Not_found

(** { 3 Check functions }
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


(** { 3 Qualify functions [qualify_* name] return the qualified name
    matching [name] in the global env scope (current module :: opened modules).
    @raise [Not_found] if not in scope } *)

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


(** { 3 Fresh functions return a fresh qualname for the current module } *)

let rec fresh_value name =
  let q = current_qual ("__" ^ name ^ "_" ^ Misc.gen_symbol()) in
  if QualEnv.mem q g_env.values
  then fresh_value name
  else q

let rec fresh_type name =
  let q = current_qual ("__" ^ name ^ "_" ^ Misc.gen_symbol()) in
  if QualEnv.mem q g_env.types
  then fresh_type name
  else q

let rec fresh_const name =
  let q = current_qual ("__" ^ name ^ "_" ^ Misc.gen_symbol()) in
  if QualEnv.mem q g_env.consts
  then fresh_const name
  else q

let rec fresh_constr name =
  let q = current_qual ("__" ^ name ^ "_" ^ Misc.gen_symbol()) in
  if QualEnv.mem q g_env.constrs
  then fresh_constr name
  else q


exception Undefined_type of qualname

(** @return the unaliased version of a type. @raise Undefined_type *)
let rec unalias_type t = match t with
  | Tid ty_name ->
      (try
        match find_type ty_name with
          | Talias ty -> unalias_type ty
          | _ -> t
      with Not_found -> raise (Undefined_type ty_name))
  | Tarray (ty, n) -> Tarray(unalias_type ty, n)
  | Tprod ty_list -> Tprod (List.map unalias_type ty_list)


(** Return the current module as a [module_object] *)
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



