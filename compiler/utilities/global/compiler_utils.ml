(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
open Misc
open Location
open Minils

let lexical_error err loc =
  Format.eprintf "%aIllegal character.@." print_location loc;
  raise Error

let syntax_error loc =
  Format.eprintf "%aSyntax error.@." print_location loc;
  raise Error

let language_error lang =
  Format.eprintf "Unknown language: '%s'.@." lang

let separateur = "\n*********************************************\
    *********************************\n*** "

let comment ?(sep=separateur) s =
  if !verbose then Format.printf "%s%s@." sep s

let do_pass d f p pp =
  comment (d^" ...\n");
  let r = f p in
  pp r;
  comment ~sep:"*** " (d^" done.");
  r

let do_silent_pass d f p = do_pass d f p (fun x -> ())

let pass d enabled f p pp =
  if enabled
  then do_pass d f p pp
  else p

let silent_pass d enabled f p =
  if enabled
  then do_silent_pass d f p
  else p

let build_path suf =
  match !target_path with
    | None -> suf
    | Some path -> Filename.concat path suf

let filename_of_name n =
  String.uncapitalize n

let clean_dir dir =
  if Sys.file_exists dir && Sys.is_directory dir
  then begin
    let rm_file_in_dir fn = Sys.remove (Filename.concat dir fn) in
    Array.iter rm_file_in_dir (Sys.readdir dir);
  end else Unix.mkdir dir 0o740;
  dir

let init_compiler modname =
  Modules.initialize modname;
  Initial.initialize ()

let lexbuf_from_file file_name =
  let ic = open_in file_name in
  let lexbuf = Lexing.from_channel ic in
  lexbuf.Lexing.lex_curr_p <-
      { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = file_name };
  ic, lexbuf



let doc_verbose = "\t\t\tSet verbose mode"
and doc_version = "\t\tThe version of the compiler"
and doc_print_types = "\t\t\tPrint types"
and doc_include = "<dir>\t\tAdd <dir> to the list of include directories"
and doc_stdlib = "<dir>\t\tDirectory for the standard library"
and doc_object_file = "\t\tOnly generate a .epo object file"
and doc_sim = "<node>\t\tCreate simulation for node <node>"
and doc_locate_stdlib = "\t\tLocate standard libray"
and doc_no_pervasives = "\tDo not load the pervasives module"
and doc_flatten = "\t\tInline everything."
and doc_target =
  "<lang>\tGenerate code in language <lang>\n\t\t\t(with <lang>=c,"
  ^ " java or z3z)"
and doc_full_type_info = "\t\t\tPrint full type information"
and doc_target_path =
  "<path>\tGenerated files will be placed in <path>\n\t\t\t(the directory is"
  ^ " cleaned)"
and doc_noinit = "\t\tDisable initialization analysis"
and doc_assert = "<node>\t\tInsert run-time assertions for boolean node <node>"
and doc_inline = "<node>\t\tInline node <node>"

let errmsg = "Options are:"

