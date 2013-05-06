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
open Graph
open Interference_graph

(** Printing *)

module DotG = struct
  include G

  let name = ref ""

  let color_to_graphviz_color i =
    (* (i * 8364263947 + 855784368) *)
    (i * 2 + 1)

  (*Functions for printing the graph *)
  let default_vertex_attributes _ = []
  let default_edge_attributes _ = []
  let get_subgraph _ = None

  let graph_attributes _ =
    [`Label !name]

  let vertex_name v =
    let rec ivar_name iv =
      match iv with
        | Ivar id -> Idents.name id
        | Ifield(ivar, f) -> (ivar_name ivar)^"_"^(Names.shortname f)
        | Imem id -> "mem("^Idents.name id^")"
        | Iwhen _ -> assert false
    in
      Misc.sanitize_string (ivar_name (List.hd !(V.label v)))

  let vertex_attributes v =
    Format.fprintf Format.str_formatter "%a" print_ivar_list !(V.label v);
    let s = Format.flush_str_formatter () in
      [`Label s; `Color (color_to_graphviz_color (Mark.get v))]

  let edge_attributes e =
    let style =
      match E.label e with
        | Iinterference -> `Solid
        | Iaffinity -> `Dashed
        | Isame_value -> `Dotted
    in
      [`Style style; `Dir `None]
end

module DotPrint = Graphviz.Dot(DotG)

let print_graph label filename g =
  Global_printer.print_type Format.str_formatter g.g_type;
  let ty_str = Format.flush_str_formatter () in
  DotG.name := label^" : "^ty_str;
  let oc = open_out (filename ^ ".dot") in
    DotPrint.output_graph oc g.g_graph;
    close_out oc
