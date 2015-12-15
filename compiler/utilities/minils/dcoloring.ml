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
open Interference_graph
open Containers

(** Coloring*)
let no_color = 0
let min_color = 1

module ColorEnv =
  ListMap(struct
    type t = int
    let compare = compare
  end)

module ColorSet =
  Set.Make(struct
    type t = int
    let compare = compare
  end)

module Dsatur = struct
  let rec remove_colored l = match l with
    | [] -> []
    | v::l -> if G.Mark.get v > 0 then l else v::(remove_colored l)

  let colors i g v =
    let color e colors =
      if G.E.label e = i then
        let c = G.Mark.get (G.E.dst e) in
          if c <> 0 then
            ColorSet.add c colors
          else
            colors
      else
        colors
    in
      G.fold_succ_e color g v ColorSet.empty

  (** Returns the smallest value not in the list of colors. *)
  let find_min_available_color interf_colors =
    let rec aux i =
      if not (ColorSet.mem i interf_colors) then i else aux (i+1)
    in
      aux min_color

  (** Returns a new color from interference and affinity colors lists.*)
  let pick_color interf_colors aff_colors =
    let aff_colors = ColorSet.diff aff_colors interf_colors in
      if not (ColorSet.is_empty aff_colors) then
        ColorSet.choose aff_colors
      else
        find_min_available_color interf_colors

  let dsat g v =
    let color_deg = ColorSet.cardinal (colors Iinterference g v) in
      if color_deg = 0 then G.out_degree g v else color_deg

  let dsat_max g v1 v2 =
    match compare (dsat g v1) (dsat g v2) with
      | 0 -> if G.out_degree g v1 > G.out_degree g v2 then v1 else v2
      | x when x > 0 -> v1
      | _ -> v2

  let uncolored_vertices g =
    G.fold_vertex (fun v acc -> if G.Mark.get v = 0 then v::acc else acc) g []

  let color_vertex g v =
    let c = (pick_color (colors Iinterference g v) (colors Iaffinity g v)) in
      G.Mark.set v c

  let rec color_vertices g vertices = match vertices with
    | [] -> ()
    | v::vertices ->
        let vmax = List.fold_left (dsat_max g) v vertices in
          color_vertex g vmax;
          let vertices = remove_colored (v::vertices) in
            color_vertices g vertices

  let coloring g =
    color_vertices g (uncolored_vertices g)
end

let values_by_color g =
  let env = G.fold_vertex
    (fun n env -> ColorEnv.add_elements (G.Mark.get n) !(G.V.label n) env)
    g.g_graph ColorEnv.empty
  in
    ColorEnv.fold (fun _ v acc -> v::acc) env []

let color g =
  Dsatur.coloring g.g_graph
