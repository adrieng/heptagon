open Graph

type ilink =
    | Iinterference
    | Iaffinity
    | Isame_value

type ivar =
    | Ivar of Idents.var_ident
    | Ifield of ivar * Names.field_name

module IvarEnv =
    Map.Make (struct
      type t = ivar
      let compare = compare
    end)

module IvarSet =
    Set.Make (struct
      type t = ivar
      let compare = compare
    end)

let rec ivar_to_string = function
  | Ivar n -> Idents.name n
  | Ifield(iv,f) -> (ivar_to_string iv)^"."^(Names.shortname f)

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
