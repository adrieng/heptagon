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
open Location
open Format
open Unix
open Compiler_options

type lexical_error =
  | Illegal_character
  | Unterminated_comment
  | Bad_char_constant
  | Unterminated_string

let lexical_error err loc =
  Format.eprintf (match err with
    | Illegal_character -> Pervasives.format_of_string "%aIllegal character.@."
    | Unterminated_comment -> "%aUnterminated comment.@."
    | Bad_char_constant -> "%aBad char constant.@."
    | Unterminated_string -> "%aUnterminated string.@."
     ) print_location loc;
  raise Errors.Error

let syntax_error loc =
  Format.eprintf "%aSyntax error.@." print_location loc;
  raise Errors.Error

let language_error lang =
  Format.eprintf "Unknown language: '%s'.@." lang

let separateur = "\n*********************************************\
    *********************************\n*** "

let comment ?(sep=separateur) s =
  if !verbose then Format.printf "%s%s@." sep s

let info: ('a, formatter, unit, unit) format4 -> 'a = fun f ->
  if !verbose then
    kfprintf (kfprintf (fun fmt -> fprintf fmt "@]@.")) err_formatter
      "Info: @[" f
  else ifprintf err_formatter f

let warn ?(cond = true): ('a, formatter, unit, unit) format4 -> 'a = fun f ->
  if cond then
    kfprintf (kfprintf (fun fmt -> fprintf fmt "@]@.")) err_formatter
      "Warning: @[" f
  else ifprintf err_formatter f

let error: ('a, formatter, unit, unit) format4 -> 'a = fun f ->
  kfprintf (kfprintf (fun fmt -> fprintf fmt "@]@.")) err_formatter
    "Error: @[" f

let do_pass d f p pp =
  comment (d ^ " ...\n");
  let _start = Unix.gettimeofday () in
  let r = Compiler_timings.time_pass d f p in
  let _stop = Unix.gettimeofday () in
  pp r;
  comment ~sep:"*** " (d ^ " done.");
  r

let do_silent_pass d f p = do_pass d f p (fun _ -> ())

let pass d enabled f p pp =
  if enabled
  then do_pass d f p pp
  else p

let silent_pass d enabled f p =
  if enabled
  then do_silent_pass d f p
  else p

let filename_of_name n =
  String.uncapitalize_ascii n

let build_path suf =
  match !target_path with
    | None -> suf
    | Some path -> Filename.concat path suf

let clean_dir dir =
  if Sys.file_exists dir && Sys.is_directory dir
  then begin
    let rm_file_in_dir fn =
      let f = Filename.concat dir fn in
      if not (Sys.is_directory f) then Sys.remove f
    in
    Array.iter rm_file_in_dir (Sys.readdir dir);
  end else Unix.mkdir dir 0o740;
  dir

let ensure_dir dir =
  if not (Sys.file_exists dir && Sys.is_directory dir)
  then Unix.mkdir dir 0o740



exception Cannot_find_file of string

let findfile filename =
  if Sys.file_exists filename then
    filename
  else if not(Filename.is_implicit filename) then
    raise(Cannot_find_file filename)
  else
    let rec find = function
      | [] -> raise(Cannot_find_file filename)
      | a::rest ->
          let b = Filename.concat a filename in
          if Sys.file_exists b then b else find rest in
    find !load_path

let lexbuf_from_file file_name =
  let ic = open_in file_name in
  let lexbuf = Lexing.from_channel ic in
  lexbuf.Lexing.lex_curr_p <-
      { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = file_name };
  ic, lexbuf

let print_header_info ff cbeg cend =
  let tm = Unix.localtime (Unix.time ()) in
  fprintf ff "%s --- Generated the %d/%d/%d at %d:%d --- %s@\n"
    cbeg tm.tm_mday (tm.tm_mon+1) (tm.tm_year + 1900) tm.tm_hour tm.tm_min cend;
  fprintf ff "%s --- heptagon compiler, version %s (compiled %s) --- %s@\n"
    cbeg version date cend;
  fprintf ff "%s --- Command line: %a--- %s@\n@\n"
    cbeg
    (fun ff a ->
       Array.iter (fun arg -> fprintf ff "%s " arg) a)
    Sys.argv
    cend

let errmsg = "Options are:"
