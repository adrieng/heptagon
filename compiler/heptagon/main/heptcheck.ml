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

(* Checks the validity of a Heptagon file (interface or implementation).*)

open Misc
open Compiler_utils
open Hept_compiler
open Location


let check_implementation modul filename =
  (* input and output files *)
  let source_name = filename ^ ".ept" in

  let ic, lexbuf = lexbuf_from_file source_name in
  let close_all_files () =
    close_in ic
  in

  try
    Initial.initialize modul;
    add_include (Filename.dirname filename);

    (* Parsing of the file *)
    let p = do_silent_pass "Parsing" (parse_implementation modul) lexbuf in

    (* Fuse static exps together *)
    let p = do_silent_pass "Static Scoping"
      Hept_static_scoping.program p in
    (* Convert the parse tree to Heptagon AST *)
    let p = do_pass "Scoping" Hept_scoping.translate_program p pp in

    (* Call the compiler*)
    let _ = compile_impl pp p in

    close_all_files ()

  with x -> close_all_files (); raise x


let main () =
  try
    Arg.parse
      [
        "-v",Arg.Set verbose, doc_verbose;
        "-version", Arg.Unit show_version, doc_version;
        "-i", Arg.Set print_types, doc_print_types;
        "-I", Arg.String add_include, doc_include;
        "-where", Arg.Unit locate_stdlib, doc_locate_stdlib;
        "-stdlib", Arg.String set_stdlib, doc_stdlib;
        "-nopervasives", Arg.Unit set_no_pervasives, doc_no_pervasives;
        "-noinit", Arg.Clear init, doc_noinit;
        "-fti", Arg.Set full_type_info, doc_full_type_info;
      ]
      (compile check_implementation)
      errmsg;
  with
    | Errors.Error -> exit 2;;

main ()


