(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* global symbol tables *)


open Misc
open Signature
open Names
open Types

exception Already_defined

exception Cannot_find_file of string

(** Warning: Whenever this type is modified,
    interface_format_version in signature.ml should be incremented. *)
type env =
    { mutable name: string;
      mutable values: node NamesEnv.t;
      mutable types: type_def NamesEnv.t;
      mutable constr: ty NamesEnv.t;
      mutable structs: structure NamesEnv.t;
      mutable fields: name NamesEnv.t;
      mutable consts: const_def NamesEnv.t;
      format_version : string;
    }

type modules =
    { current: env;                (* associated symbol table *)
      mutable opened: env list;    (* opened tables *)
      mutable modules: env NamesEnv.t;  (* tables loaded in memory *)
    }

let current =
  { name = ""; values = NamesEnv.empty; types = NamesEnv.empty;
    constr = NamesEnv.empty; structs = NamesEnv.empty; fields = NamesEnv.empty;
    consts = NamesEnv.empty; format_version = interface_format_version }

let modules =
  { current = current; opened = []; modules = NamesEnv.empty }

let findfile filename =
  if Sys.file_exists filename then
    filename
  else if not(Filename.is_implicit filename) then
    raise(Cannot_find_file filename)
  else
    let rec find = function
        [] ->
          raise(Cannot_find_file filename)
      | a::rest ->
          let b = Filename.concat a filename in
          if Sys.file_exists b then b else find rest
    in find !load_path

let load_module modname =
  let name = String.uncapitalize modname in
  try
    let filename = findfile (name ^ ".epci") in
    let ic = open_in_bin filename in
    try
      let m:env = input_value ic in
      if m.format_version <> interface_format_version then (
        Format.eprintf "The file %s was compiled with \
                       an older version of the compiler.\n \
                       Please recompile %s.ept first.@." filename name;
        raise Error
      );
      close_in ic;
      m
    with
      | End_of_file | Failure _ ->
          close_in ic;
          Format.eprintf "Corrupted compiled interface file %s.\n\
                        Please recompile %s.ept first.@." filename name;
          raise Error
  with
    | Cannot_find_file(filename) ->
        Format.eprintf "Cannot find the compiled interface file %s.@."
          filename;
        raise Error

let find_module modname =
  try
    NamesEnv.find modname modules.modules
  with
      Not_found ->
        let m = load_module modname in
        modules.modules <- NamesEnv.add modname m modules.modules;
        m


type 'a info = { qualid : qualident; info : 'a }

let find where qualname =
  let rec findrec ident = function
    | [] -> raise Not_found
    | m :: l ->
        try { qualid = { qual = m.name; id = ident };
              info = where ident m }
        with Not_found -> findrec ident l in

  match qualname with
    | Modname({ qual = m; id = ident } as q) ->
        let current = if current.name = m then current else find_module m in
        { qualid = q; info = where ident current }
    | Name(ident) -> findrec ident (current :: modules.opened)

(* exported functions *)
let open_module modname =
  let m = find_module modname in
  modules.opened <- m :: modules.opened

let initialize modname =
  current.name <- modname;
  List.iter open_module !default_used_modules

let add_value f signature =
  if NamesEnv.mem f current.values then raise Already_defined;
  current.values <- NamesEnv.add f signature current.values
let add_type f type_def =
  if NamesEnv.mem f current.types then raise Already_defined;
  current.types <- NamesEnv.add f type_def current.types
let add_constr f ty_res =
  if NamesEnv.mem f current.constr then raise Already_defined;
  current.constr <- NamesEnv.add f ty_res current.constr
let add_struct f fields =
  if NamesEnv.mem f current.structs then raise Already_defined;
  current.structs <- NamesEnv.add f fields current.structs
let add_field f n =
  if NamesEnv.mem f current.fields then raise Already_defined;
  current.fields <- NamesEnv.add f n current.fields
let add_const f n =
  if NamesEnv.mem f current.consts then raise Already_defined;
  current.consts <- NamesEnv.add f n current.consts

let add_value_by_longname ln signature =
  match ln with
    | Modname { qual = modname; id = f } ->
        let m =
          if modname = current.name then
            current
          else
            NamesEnv.find modname modules.modules in
          if not (NamesEnv.mem f m.values) then
            m.values <- NamesEnv.add f signature m.values
    | Name _ -> raise Not_found

let find_value = find (fun ident m -> NamesEnv.find ident m.values)
let find_type = find (fun ident m -> NamesEnv.find ident m.types)
let find_constr = find (fun ident m -> NamesEnv.find ident m.constr)
let find_struct = find (fun ident m -> NamesEnv.find ident m.structs)
let find_field = find (fun ident m -> NamesEnv.find ident m.fields)
let find_const = find (fun ident m -> NamesEnv.find ident m.consts)

let replace_value f signature =
  current.values <- NamesEnv.remove f current.values;
  current.values <- NamesEnv.add f signature current.values

let write oc = output_value oc current

let longname n = Modname({ qual = current.name; id = n })
let currentname longname =
  match longname with
    | Name(n) -> longname
    | Modname{ qual = q; id = id} ->
        if current.name = q then Name(id) else longname

exception Undefined_type of longname
(** @return the unaliased version of a type. *)
let rec unalias_type = function
  | Tid ty_name ->
      (try
        let { qualid = q; info = ty_desc } = find_type ty_name in
          match ty_desc with
            | Talias ty -> unalias_type ty
            | _ -> Tid (Modname q)
      with Not_found -> raise (Undefined_type ty_name))
  | Tarray (ty, n) -> Tarray(unalias_type ty, n)
  | Tprod ty_list -> Tprod (List.map unalias_type ty_list)
