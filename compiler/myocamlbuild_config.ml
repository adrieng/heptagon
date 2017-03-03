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
open Ocamlbuild_plugin

(* this is supposed to list available syntaxes, but I don't know how to do it. *)
let find_syntaxes () = ["camlp4o"; "camlp4r"]

let ocamlfind_query pkg =
  let cmd = Printf.sprintf "ocamlfind query %s" (Filename.quote pkg) in
  Ocamlbuild_pack.My_unix.run_and_open cmd (fun ic -> input_line ic)

let ocamlfind_after_rules () =

  (* Like -package but for extensions syntax. Morover -syntax is useless
   * when linking. *)
  List.iter begin fun syntax ->
    flag ["ocaml"; "compile";  "syntax_"^syntax] & S[A"-syntax"; A syntax];
    flag ["ocaml"; "ocamldep"; "syntax_"^syntax] & S[A"-syntax"; A syntax];
    flag ["ocaml"; "doc";      "syntax_"^syntax] & S[A"-syntax"; A syntax];
    flag ["ocaml"; "infer_interface"; "syntax_"^syntax] & S[A"-syntax"; A syntax];
  end (find_syntaxes ());

  flag ["ocaml"; "doc"; "thread"] & S[A"-I"; A"+threads"];

  (* Use both ml and mli files to build documentation: *)
  rule "ocaml: ml & mli -> odoc"
    ~insert:`top
    ~prod:"%.odoc"
    (* "%.cmo" so that cmis of ml dependencies are already built: *)
    ~deps:["%.ml"; "%.mli"; "%.cmo"]
    begin fun env build ->
      let mli = env "%.mli" and ml = env "%.ml" and odoc = env "%.odoc" in
      let tags =
        (Tags.union (tags_of_pathname mli) (tags_of_pathname ml))
        ++"doc_use_interf_n_implem"++"ocaml"++"doc" in
      let include_dirs = Pathname.include_dirs_of (Pathname.dirname ml) in
      let include_flags =
        List.fold_right (fun p acc -> A"-I" :: A p :: acc) include_dirs [] in
      Cmd (S [!Options.ocamldoc; A"-dump"; Px odoc;
              T (tags++"doc"++"pp"); S (include_flags);
              A"-intf"; P mli; A"-impl"; P ml])
    end;

  (* Specifying merge options. *)
  pflag ["ocaml"; "doc"; "doc_use_interf_n_implem"] "merge"
    (fun s -> S[A"-m"; A s]);
