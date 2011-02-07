(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
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

let do_pass d f p pp =
  comment (d^" ...\n");
  let r = f p in
  pp r;
  comment ~sep:"*** " (d^" done.");
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



let build_path suf =
  match !target_path with
    | None -> suf
    | Some path -> Filename.concat path suf

let clean_dir dir =
  if Sys.file_exists dir && Sys.is_directory dir
  then begin
    let rm_file_in_dir fn = Sys.remove (Filename.concat dir fn) in
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

