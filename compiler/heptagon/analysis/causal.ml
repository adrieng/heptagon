(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* causality check of scheduling constraints *)

open Misc
open Names
open Idents
open Heptagon
open Location
open Graph
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
  | Clastread of ident
  | Cempty

(* normalized constraints *)
type ac =
  | Awrite of ident
  | Aread of ident
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
  raise Misc.Error

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

let rec ctuple l =
  let rec norm_or l res = match l with
    | [] -> Aac (Atuple (List.rev res))
    | Aempty::l -> norm_or l res
    | Aor (Aempty, nc2)::l -> norm_or (nc2::l) res
    | Aor (nc1, Aempty)::l -> norm_or (nc1::l) res
    | Aor(nc1, nc2)::l ->
        Aor(norm_or (nc1::l) res, norm_or (nc2::l) res)
    | (Aac ac)::l -> norm_or l (ac::res)
  in
    norm_or l []

and norm = function
  | Cor(c1, c2) -> cor (norm c1) (norm c2)
  | Cand(c1, c2) -> cand (norm c1) (norm c2)
  | Cseq(c1, c2) -> cseq (norm c1) (norm c2)
  | Ctuple l -> ctuple (List.map norm l)
  | Cwrite(n) -> Aac(Awrite(n))
  | Cread(n) -> Aac(Aread(n))
  | Clastread(n) -> Aac(Alastread(n))
  | _ -> Aempty

(* building a dependence graph from a scheduling constraint *)
let build ac =
  (* associate a graph node for each name declaration *)
  let nametograph n g n_to_graph = Env.add n g n_to_graph in

  let rec associate_node g n_to_graph = function
    | Awrite(n) ->
        nametograph n g n_to_graph
    | Atuple l ->
        List.fold_left (associate_node g) n_to_graph l
    | _ ->
        n_to_graph
  in

  (* first build the association [n -> node] *)
  (* for every defined variable *)
  let rec initialize ac n_to_graph =
    match ac with
      | Aand(ac1, ac2) ->
          let n_to_graph = initialize ac1 n_to_graph in
          initialize ac2 n_to_graph
      | Aseq(ac1, ac2) ->
          let n_to_graph = initialize ac1 n_to_graph in
          initialize ac2 n_to_graph
      | _ ->
          let g = make ac in
          associate_node g n_to_graph ac
  in

  let make_graph ac n_to_graph =
    let attach node n =
      try
        let g = Env.find n n_to_graph in add_depends node g
      with
        | Not_found -> () in

    let rec add_dependence g = function
      | Aread(n) -> attach g n
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
        | Atuple l ->
            begin try
              node_for_tuple l
            with Not_found
                _ -> make ac
            end
        | _ -> make ac
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
        | Aread(n) -> let g = make ac in attach g n; [g], [g]
        | Atuple(l) ->
            let make_graph_tuple ac =
              match ac with
                | Aand _ | Atuple _ -> make_graph ac
                | _ -> [], []
            in
            let g = node_for_ac ac in
            List.iter (add_dependence g) l;
            let top_l, bot_l = List.split (List.map make_graph_tuple l) in
            let top_l = List.flatten top_l in
            let bot_l = List.flatten bot_l in
            g::top_l, g::bot_l
        | _ -> [], []

    in
    let top_list, bot_list = make_graph ac in
    graph top_list bot_list in

  let n_to_graph = initialize ac Env.empty in
  let g = make_graph ac n_to_graph in
  g

(* the main entry. *)
let check loc c =
  let check_ac ac =
    let { g_bot = g_list } = build ac in
    match cycle g_list with
      | None -> ()
      | Some _ -> error (Ecausality_cycle ac) in

  let rec check = function
    | Aempty -> ()
    | Aac(ac) -> check_ac ac
    | Aor(nc1, nc2) -> check nc1; check nc2 in

  let nc = norm c in
  try
    check nc
  with
    | Error(kind) -> message loc kind
