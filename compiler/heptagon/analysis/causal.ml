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

(* causality check of scheduling constraints *)

open Idents
open Location
open Sgraph
open Format
open Pp_tools

(* x = x + 1 is rejected because read(x) < write(x) is not causal *)
(* build a dependency graph an checks for cycles *)
(* for the moment, the # constructor is distributed which leads to a *)
(* sub-optimal algorithm. *)

(* constraints [c] are normalised into [a1 # ... # an] st: *)
(* a ::= write(x) | read(x) | last(x) | a < a | a || a *)
(* c ::= a # ... # a *)
(* a constraint [a] is causal if its dependence graph is acyclic *)

(* scheduling constraints *)
type sc =
  | Cor of sc * sc
  | Cand of sc * sc
  | Cseq of sc * sc
  | Ctuple of sc list
  | Cwrite of ident
  | Cread of ident
  | Clinread of ident
  | Clastread of ident
  | Cempty

(* normalized constraints *)
type ac =
  | Awrite of ident
  | Aread of ident
  | Alinread of ident
  | Alastread of ident
  | Aseq of ac * ac
  | Aand of ac * ac
  | Atuple of ac list

and nc =
  | Aor of nc * nc
  | Aac of ac
  | Aempty

let output_ac ff ac =
  let rec print priority ff ac = match ac with
    | Aseq(ac1, ac2) -> (* priority 1 *)
        (if priority = 1 then fprintf ff "%a@ < %a"
         else if priority > 1
         then fprintf ff "@[<v 1>(%a@ < %a)@]"
         else fprintf ff "@[%a@ < %a@]")
          (print 1) ac1 (print 1) ac2
    | Aand(ac1, ac2) -> (* priority 0 *)
        (if priority = 0 then fprintf ff "%a@ || %a"
         else if priority > 0
         then fprintf ff "@[<v 1>(%a@ || %a)@]"
         else fprintf ff "@[%a@ || %a@]")
          (print 0) ac1 (print 0) ac2
    | Atuple(acs) ->
        fprintf ff "@[%a@]" (print_list_r (print 1) "(" "," ")") acs
    | Awrite(m) -> fprintf ff "%s" (name m)
    | Aread(m) -> fprintf ff "^%s" (name m)
    | Alinread(m) -> fprintf ff "*%s" (name m)
    | Alastread(m) -> fprintf ff "last %s" (name m)
  in
  fprintf ff "@[<v 1>%a@]@?" (print 0) ac


type error =  Ecausality_cycle of ac

exception Error of error

let error kind = raise (Error(kind))

let message loc kind =
  begin match kind with
    | Ecausality_cycle(ac) ->
        eprintf
          "%aCausality error: the following constraint is not causal.@\n%a@."
          print_location loc
          output_ac ac
  end;
  raise Errors.Error

let cor nc1 nc2 =
  match nc1, nc2 with
    | Aempty, Aempty -> Aempty
    | _ -> Aor(nc1, nc2)

let rec cseq nc1 nc2 =
  match nc1, nc2 with
    | Aempty, _ -> nc2
    | _, Aempty -> nc1
    | Aor(nc1, nc11), nc2 -> Aor(cseq nc1 nc2, cseq nc11 nc2)
    | nc1, Aor(nc2, nc22) -> Aor(cseq nc1 nc2, cseq nc1 nc22)
    | Aac(ac1), Aac(ac2) -> Aac(Aseq(ac1, ac2))

let rec cand nc1 nc2 =
  match nc1, nc2 with
    | Aempty, _ -> nc2 | _, Aempty -> nc1
    | Aor(nc1, nc11), nc2 -> Aor(cand nc1 nc2, cand nc11 nc2)
    | nc1, Aor(nc2, nc22) -> Aor(cand nc1 nc2, cand nc1 nc22)
    | Aac(ac1), Aac(ac2) -> Aac(Aand(ac1, ac2))

let mk_tuple l = match l with
  | [] -> Aempty
  | [ac] -> Aac ac
  | _ -> Aac (Atuple l)

let rec ctuple l =
  let rec norm_tuple l before newl = match l with
    | [] -> cseq before (mk_tuple newl)
    | Aempty::l -> norm_tuple l before newl
    | (Aac ((Awrite _ | Aread _ | Alinread _ | Alastread _) as ac))::l ->
      norm_tuple l before (ac::newl)
    | ((Aac _) as ac)::l ->
      norm_tuple l (cand before ac) newl
    | (Aor _)::_ -> assert false
  in
  norm_tuple l Aempty []

and norm = function
  | Cor(c1, c2) -> cor (norm c1) (norm c2)
  | Cand(c1, c2) -> cand (norm c1) (norm c2)
  | Cseq(c1, c2) -> cseq (norm c1) (norm c2)
  | Ctuple l -> ctuple (List.map norm l)
  | Cwrite(n) -> Aac(Awrite(n))
  | Cread(n) -> Aac(Aread(n))
  | Clinread(n) -> Aac(Alinread(n))
  | Clastread(n) -> Aac(Alastread(n))
  | _ -> Aempty

exception Self_dependency

(* building a dependence graph from a scheduling constraint *)
let build ac =
  (* associate a graph node for each name declaration *)
  let nametograph n g n_to_graph = Env.add n g n_to_graph in

  let rec associate_node g (n_to_graph, lin_map) = function
    | Awrite(n) ->
        nametograph n g n_to_graph, lin_map
    | Alinread(n) ->
        n_to_graph, nametograph n g lin_map
    | Atuple l ->
        List.fold_left (associate_node g) (n_to_graph, lin_map) l
    | _ ->
        n_to_graph, lin_map
  in

  (* first build the association [n -> node] *)
  (* for every defined variable *)
  let rec initialize ac n_to_graph lin_map =
    match ac with
      | Aand(ac1, ac2) ->
          let n_to_graph, lin_map = initialize ac1 n_to_graph lin_map in
          initialize ac2 n_to_graph lin_map
      | Aseq(ac1, ac2) ->
          let n_to_graph, lin_map = initialize ac1 n_to_graph lin_map in
          initialize ac2 n_to_graph lin_map
      | _ ->
          let g = make ac in
          associate_node g (n_to_graph, lin_map) ac
  in

  let make_graph ac n_to_graph lin_map =
    let attach node n =
      try
        let g = Env.find n n_to_graph in
        if g.g_tag = node.g_tag then
          raise Self_dependency
        else
          add_depends node g
      with
        | Not_found -> () in

    let attach_lin node n =
      try
        let g = Env.find n lin_map in
        if g.g_tag = node.g_tag then
          raise Self_dependency
        else
          add_depends g node
      with
        | Not_found -> () in

    let add_dependence g = function
      | Aread(n) -> attach g n; attach_lin g n
      | Alinread(n) -> attach g n
      | _ -> ()
    in

    let rec node_for_ac ac =
      let rec node_for_tuple = function
        | [] -> raise Not_found
        | v::l ->
            (try
               node_for_ac v
             with
                 Not_found -> node_for_tuple l
            )
      in
      match ac with
        | Awrite n -> Env.find n n_to_graph
        | Alinread n -> Env.find n lin_map
        | Atuple l ->
            (try
                node_for_tuple l
              with Not_found -> make ac)
        | _ -> raise Not_found
    in

    let rec make_graph ac =
      match ac with
        | Aand(ac1, ac2) ->
            let top1, bot1 = make_graph ac1 in
            let top2, bot2 = make_graph ac2 in
            top1 @ top2, bot1 @ bot2
        | Aseq(ac1, ac2) ->
            let top1, bot1 = make_graph ac1 in
            let top2, bot2 = make_graph ac2 in
            (* add extra dependences *)
            List.iter
              (fun top -> List.iter (fun bot -> add_depends top bot) bot1)
              top2;
            top1 @ top2, bot1 @ bot2
        | Awrite(n) -> let g = Env.find n n_to_graph in [g], [g]
        | Aread(n) ->let g = make ac in attach g n; attach_lin g n; [g], [g]
        | Alinread(n) -> let g = Env.find n lin_map in attach g n; [g], [g]
        | Atuple(l) ->
            let g = node_for_ac ac in
            List.iter (add_dependence g) l; [g], [g]
        | _ -> [], []

    in
    let top_list, bot_list = make_graph ac in
    graph top_list bot_list in

  let n_to_graph, lin_map = initialize ac Env.empty Env.empty in
  let g = make_graph ac n_to_graph lin_map in
  g

(* the main entry. *)
let check loc c =
  let check_ac ac =
    try
      (let { g_bot = g_list } = build ac in
      match cycle g_list with
        | None -> ()
        | Some _ -> error (Ecausality_cycle ac))
    with
      | Self_dependency -> error (Ecausality_cycle ac)
  in


  let rec check = function
    | Aempty -> ()
    | Aac(ac) -> check_ac ac
    | Aor(nc1, nc2) -> check nc1; check nc2 in

  let nc = norm c in
  try
    check nc
  with
    | Error(kind) -> message loc kind
