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
(* graph manipulation *)

type 'a graph =
    { g_top: 'a node list;
      g_bot: 'a node list }

and 'a node =
    { g_containt: 'a;
      g_tag: int;
      mutable g_visited: bool;
      mutable g_mark: int;
      mutable g_depends_on: 'a node list;
      mutable g_depends_by: 'a node list;
    }

exception Cycle of int (* returns the index of the node *)

let tag = ref 0
let new_tag () = incr tag; !tag
let containt g = g.g_containt
let linked g1 g2 =
  (List.memq g2 g1.g_depends_on) || (List.memq g1 g2.g_depends_on)
let make c =
  { g_containt = c; g_tag = new_tag (); g_visited = false;
    g_mark = -1; g_depends_on = []; g_depends_by = [] }
let add_depends node1 node2 =
  if not (node1.g_tag = node2.g_tag) then (
    node1.g_depends_on <- node2 :: node1.g_depends_on;
    node2.g_depends_by <- node1 :: node2.g_depends_by
  )

let remove_depends node1 node2 =
  if not (node1.g_tag = node2.g_tag)
  then (
    node1.g_depends_on <-
      List.filter (fun n -> n.g_tag <> node2.g_tag) node1.g_depends_on;
    node2.g_depends_by <-
      List.filter (fun n -> n.g_tag <> node1.g_tag) node2.g_depends_by
  )

let graph top_list bot_list = { g_top = top_list; g_bot = bot_list }


let topological g_list =
  let rec sortrec g_list seq =
    match g_list with
      | [] -> seq
      | g :: g_list ->
          if g.g_visited then sortrec g_list seq
          else
            begin
              g.g_visited <- true;
              let seq = sortrec g.g_depends_on seq in
              sortrec g_list (g :: seq)
            end in
  let seq = sortrec g_list [] in
  List.iter
    (fun ({ g_visited = _ } as node) -> node.g_visited <- false) g_list;
  List.rev seq

(** Detection of cycles *)
(* Mark nodes with:
   - -1 initially, for unvisited nodes
   - 0 for "opened" nodes, currently visited, while visiting its descendents
   - 1 for "closed" nodes, visited once, no circuits found from it.
   A circuit is found when a node marked with 0 is visited again.
*)

let cycle g_list =
  (* store nodes in a stack *)
  let s = Stack.create () in
  (* flush the connected component *)
  let rec flush _index =
    if Stack.is_empty s then []
    else let v = Stack.pop s in
    v.g_containt :: flush v.g_tag in

  let rec visit g =
    match g.g_mark with
      | -1 ->
          (* Unvisited yet *)
          (* Open node *)
          Stack.push g s;
          g.g_mark <- 0;
          (* Visit descendents *)
          List.iter visit g.g_depends_on;
          (* Close node *)
          ignore (Stack.pop s);
          g.g_mark <- 1
      | 0 ->
          (* Visit an opened node (visited and not close) : circuit *)
          raise (Cycle g.g_tag)
      | 1 | _ ->
          (* Visit a closed node (no existing circuit) : pass *)
          () in
  try
    List.iter visit g_list; None
  with
    | Cycle(index) -> Some(flush index)

(** [accessible useful_nodes g_list] returns the list of
    accessible nodes starting from useful_nodes and belonging to
    g_list. *)
let accessible useful_nodes g_list =
  let rec follow g =
    if not g.g_visited then
      begin
        g.g_visited <- true;
        List.iter follow g.g_depends_on
      end in
  let read acc g =
    if g.g_visited then begin g.g_visited <- false; g :: acc end else acc in
  List.iter follow useful_nodes;
  List.fold_left read [] g_list

(** [exists_path nodes n1 n2] returns whether there is a path
    from n1 to n2 in the graph. nodes is the list of all the nodes
    in the graph. *)
let exists_path nodes n1 n2 =
  List.mem n2 (accessible [n1] nodes)

(*
open Format

let print_node print g =
  printf "Node : @[<hov>";
  print_int g.g_tag;
  printf "@]";
  printf "  Depends on :@\n";
  printf "  @[<v>";
  List.iter
    (fun node ->
       printf "@[<hov 2>";
       print_int node.g_tag;
       printf "@]@ ")
    g.g_depends_on;
  printf "@]"
*)
