(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(* Nicolas Berthier, SUMO, INRIA                                       *)
(*                                                                     *)
(* Copyright 2014 ENS, INRIA, UJF                                      *)
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
open Compiler_utils
open Names

let ctrlr_mod_suffix = "_controller"

let types_mod_suffix = "_types"

let dirname_for_modul modul =
  build_path (filename_of_name (modul_to_string modul) ^ "_ctrln")

let ctrln_for_node { qual; name } =
  dirname_for_modul qual ^"/"^ name ^".ctrln"

let ctrls_for_node { qual; name } =
  Printf.sprintf "%s/%s.%d.ctrls" (dirname_for_modul qual) name

let ctrlf_for_node { qual; name } =
  Printf.sprintf "%s/%s.ctrlf" (dirname_for_modul qual) name

let controller_modul = function
  | Module n -> Module (n ^ ctrlr_mod_suffix)
  | QualModule ({ name = n } as q) ->
      QualModule { q with name = n ^ ctrlr_mod_suffix }
  | _ -> failwith "Unexpected module"

let types_modul = function
  | Module n -> Module (n ^ types_mod_suffix)
  | QualModule ({ name = n } as q) ->
      QualModule { q with name = n ^ types_mod_suffix }
  | _ -> failwith "Unexpected module"

let controller_node ?num { qual; name } = match num with
  | Some num -> { qual = controller_modul qual;
                 name = Printf.sprintf "%s_ctrlr%d" name num }
  | None -> { qual = controller_modul qual;
             name = Printf.sprintf "%s_ctrlr0" name }

let save_controller_modul_for modul =
  let om = Modules.current () in
  let cm = controller_modul modul in
  let epci = String.uncapitalize_ascii (Names.modul_to_string cm) ^ ".epci" in
  Modules.select cm;
  (* XXX check for empty modules? *)
  let oc = open_out_bin epci in
  output_value oc (Modules.current_module ());
  close_out oc;
  Modules.select om

let init_cond_str = "__init__"                             (* XXX uniqueness? *)
let sink_state_str = "__sink__"

