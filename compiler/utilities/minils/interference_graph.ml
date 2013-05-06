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
open Format
open Pp_tools
open Global_printer
open Graph

type ilink =
    | Iinterference
    | Iaffinity
    | Isame_value

type ivar =
    | Ivar of Idents.var_ident
    | Ifield of ivar * Names.field_name
    | Iwhen of ivar * Clocks.ck
    | Imem of Idents.var_ident

let rec ivar_compare iv1 iv2 = match iv1, iv2 with
  | Ivar x1, Ivar x2 -> Idents.ident_compare x1 x2
  | Iwhen (iiv1, ck1), Iwhen (iiv2, ck2) ->
      let cr = Global_compare.clock_compare ck1 ck2 in
      if cr <> 0 then cr else ivar_compare iiv1 iiv2
  | Ifield (iiv1, f1), Ifield (iiv2, f2) ->
      let cr = Pervasives.compare f1 f2 in
      if cr <> 0 then cr else ivar_compare iiv1 iiv2
  | Imem x1, Imem x2 -> Idents.ident_compare x1 x2

  | Ivar _, _ -> 1

  | Iwhen _, Ivar _ -> -1
  | Iwhen _, _ -> 1

  | Ifield _, (Ivar _ | Iwhen _) -> -1
  | Ifield _, _ -> 1

  | Imem _, _ -> -1

module IvarEnv =
    Map.Make (struct
      type t = ivar
      let compare = ivar_compare
    end)

module IvarSet =
    Set.Make (struct
      type t = ivar
      let compare = ivar_compare
    end)

let rec print_ivar ff iv = match iv with
  | Ivar n -> print_ident ff n
  | Ifield(iv,f) -> fprintf ff "%a.%a" print_ivar iv print_qualname f
  | Iwhen(iv, ck) -> fprintf ff "%a::%a" print_ivar iv print_ck ck
  | Imem n -> fprintf ff "mem(%a)" print_ident n

let print_ivar_list ff l =
  fprintf ff "@[<2>%a@]" (print_list_r print_ivar "("","")") l

let rec var_ident_of_ivar iv = match iv with
  | Iwhen (iv, _) -> var_ident_of_ivar iv
  | Ifield (iv, _) -> var_ident_of_ivar iv
  | Ivar x -> x
  | Imem x -> x

let rec remove_iwhen iv = match iv with
  | Iwhen (iv, _) -> remove_iwhen iv
  | Ifield (iv, f) -> Ifield (remove_iwhen iv, f)
  | _ -> iv

let remove_inner_iwhen iv = match iv with
  | Iwhen (iv, ck) -> Iwhen (remove_iwhen iv, ck)
  | _ -> remove_iwhen iv

let is_when_ivar iv = match iv with
  | Iwhen _ -> true
  | _ -> false
let is_mem_ivar iv = match iv with
  | Imem _ -> true
  | _ -> false

module VertexValue = struct
  type t = ivar list ref
  (*let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
  let default = []*)
end

module EdgeValue = struct
  type t = ilink
  let default = Iinterference
  let compare = compare
end

module G =
struct
  include Imperative.Graph.AbstractLabeled(VertexValue)(EdgeValue)

  let add_edge_v g n1 v n2 =
    add_edge_e g (E.create n1 v n2)

  let mem_edge_v g n1 n2 v =
    try
      (E.label (find_edge g n1 n2)) = v
    with
        Not_found -> false

  let filter_succ g v n =
    fold_succ_e (fun e acc -> if (E.label e) = v then (E.dst e)::acc else acc) g n []

  let coalesce g n1 n2 =
    if n1 <> n2 then (
      iter_succ_e (fun e -> add_edge_e g (E.create n1 (E.label e) (E.dst e))) g n2;
      let r = V.label n1 in
        r := !(V.label n2) @ !r;
        remove_vertex g n2
    )

  let vertices g =
    fold_vertex (fun v acc -> v::acc) g []

  let filter_vertices f g =
    fold_vertex (fun v acc -> if f v then v::acc else acc) g []
end

type interference_graph = {
  g_type : Types.ty;
  g_graph : G.t;
  g_hash : (ivar, G.V.t) Hashtbl.t
}

(** Functions to create graphs and nodes *)

let mk_node x =
  G.V.create (ref [x])

let add_node g n =
  G.add_vertex g.g_graph n;
  List.iter (fun x -> Hashtbl.add g.g_hash x n) !(G.V.label n)
  (* Hashtbl.add g.g_tag_hash n.g_tag n;
  n.g_graph <- Some g*)

let node_for_value g x =
  Hashtbl.find g.g_hash x

let mk_graph nodes ty =
  let g = { g_graph = G.create ();
            g_type = ty;
            g_hash = Hashtbl.create 100 } in
    List.iter (add_node g) nodes;
    g

(** Functions to read the graph *)
let interfere g n1 n2 =
  G.mem_edge_v g.g_graph n1 n2 Iinterference

let affinity g n1 n2 =
  G.mem_edge_v g.g_graph n1 n2 Iaffinity

let have_same_value g n1 n2 =
  G.mem_edge_v g.g_graph n1 n2 Isame_value

let interfere_with g n =
  G.filter_succ g.g_graph Iinterference n

let affinity_with g n =
  G.filter_succ g.g_graph Iaffinity n

let has_same_value_as g n =
  G.filter_succ g.g_graph Isame_value n


(** Functions to modify the graph *)

let add_interference_link g n1 n2 =
  if n1 <> n2 then (
    G.remove_edge g.g_graph n1 n2;
    G.add_edge_v g.g_graph n1 Iinterference n2
  )

let add_affinity_link g n1 n2 =
  if n1 <> n2 && not (G.mem_edge g.g_graph n1 n2) then (
    G.remove_edge g.g_graph n1 n2;
    G.add_edge_v g.g_graph n1 Iaffinity n2
  )

let add_same_value_link g n1 n2 =
  if n1 <> n2 && not (interfere g n1 n2) then (
    G.remove_edge g.g_graph n1 n2;
    G.add_edge_v g.g_graph n1 Isame_value n2
  )

let coalesce g n1 n2 =
  let find_wrong_same_value () =
    let filter_same_value e acc =
      if (G.E.label e) = Isame_value && not(have_same_value g n2 (G.E.dst e)) then
        (G.E.dst e)::acc
      else
        acc
    in
      G.fold_succ_e filter_same_value g.g_graph n1 []
  in
    (* remove same value links no longer true *)
    List.iter (fun n -> G.remove_edge g.g_graph n n1) (find_wrong_same_value ());
    (* update the hash table*)
    List.iter (fun x -> Hashtbl.replace g.g_hash x n1) !(G.V.label n2);
    (* coalesce nodes in the graph*)
    G.coalesce g.g_graph n1 n2

(** Iterates [f] on all the couple of nodes interfering in the graph g *)
let iter_interf f g =
  let do_f e =
    if G.E.label e = Iinterference then
      f g (G.E.src e) (G.E.dst e)
  in
    G.iter_edges_e do_f g.g_graph
