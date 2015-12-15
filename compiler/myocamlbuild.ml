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
open Ocamlbuild_plugin.Options
open Myocamlbuild_config

let df = function
  | After_rules ->
      ocamlfind_after_rules ();

      (* Tell ocamlbuild about the camlp4 library. *)
      ocaml_lib ~extern:true ~dir:(ocamlfind_query "camlp4") "camlp4";

      (* Add preproc.cmo to the ocaml pre-processor when use_preproc is set *)
      flag ["ocaml"; "pp"; "use_preproc"] (A "preproc.cmo");

      (* Running ocamldep on ocaml code that is tagged with use_preproc will
         require the cmo.  Note that you only need this declaration when the
         syntax extension is part of the sources to be compiled with
         ocamlbuild. *)
      dep ["ocaml"; "ocamldep"; "use_preproc"] ["preproc.cmo"];

      flag ["ocaml"; "parser" ; "menhir" ; "use_menhir"] (S[A"--explain";
                                                            A"--table"]);

      flag ["ocaml"; "compile" ] (S[A"-w"; A"Ae"; A"-warn-error"; A"PU";
                                    A"-w"; A"-9-48"]);

  | _ -> ()

let _ = dispatch df
