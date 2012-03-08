(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* Unroll loops *)

open Format
open List
open Modules
open Names
open C

let rec unroll id start stop body =
  let rec aux i l =
    let rec exp e = match e with
      | Cuop (s, e) -> Cuop (s, exp e)
      | Cbop (s, e1, e2) -> Cbop (s, exp e1, exp e2)
      | Cfun_call (s, e_l) -> Cfun_call (s, List.map exp e_l)
      | Caddrof e -> Caddrof (exp e)
      | Cstructlit (s, e_l) -> Cstructlit (s, List.map exp e_l)
      | Carraylit e_l -> Carraylit (List.map exp e_l)
      | Cconst c -> Cconst c
      | Cvar s -> if s = id then Cconst (Ccint i) else Cvar s
      | Cderef e -> Cderef (exp e)
      | Cfield (e, qn) -> Cfield (exp e, qn)
      | Carray (e1, e2) -> Carray (exp e1, exp e2)

    and lhs l = match l with
      | CLvar s -> CLvar s
      | CLderef l -> CLderef (lhs l)
      | CLfield (l, qn) -> CLfield (lhs l, qn)
      | CLarray (l, e) -> CLarray (lhs l, exp e)

    and stm s = match s with
      | Csexpr e -> Csexpr (exp e)
      | Csblock b -> Csblock (block b)
      | Cskip -> Cskip
      | Caffect (l, e) -> Caffect (lhs l, exp e)
      | Cif (e, l1, l2) -> Cif (exp e, List.map stm l1, List.map stm l2)
      | Cswitch (e, cl_l) -> Cswitch (exp e, List.map (fun (s, s_l) -> s, List.map stm s_l) cl_l)
      | Cwhile (o, e, s_l) -> Cwhile (o, exp e, List.map stm s_l)
      | Cfor _ -> assert false
      | Creturn e -> Creturn (exp e)

    and block b = { b with block_body = List.map stm b.block_body; }

    in

    if i = stop then List.rev l else aux (Int32.succ i) (List.map stm body @ l)

  in

  aux start []

let rec static_eval e = match e with
  | Cconst (Ccint i) -> Some i
  | _ -> None

let rec stm s = match s with
  | Csexpr _ | Cskip | Caffect _ | Creturn _ -> s
  | Csblock b -> Csblock (block b)
  | Cif (e, l1, l2) -> Cif (e, List.map stm l1, List.map stm l2)
  | Cswitch (e, cl_l) -> Cswitch (e, List.map (fun (s, s_l) -> s, List.map stm s_l) cl_l)
  | Cwhile (o, e, s_l) -> Cwhile (o, e, List.map stm s_l)
  | Cfor (x, start, stop, body) ->
    let body = List.map stm body in
    (match static_eval start, static_eval stop with
      | Some i, Some j -> Csblock { var_decls = []; block_body = unroll x i j body; }
      | _ -> Cfor (x, start, stop, body))

and block b = { b with block_body = List.map stm b.block_body; }

let cdef d = match d with
  | Cfundef def ->
    let body = { def.f_body with block_body = List.map stm def.f_body.block_body; } in
    Cfundef { def with f_body = body; }
  | _ -> d

let cfile (s, d) = match d with
  | Cheader _ -> (s, d)
  | Csource cdl -> (s, Csource (List.map cdef cdl))
