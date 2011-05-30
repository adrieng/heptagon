(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* control optimisation *)

open Idents
open Misc
open Obc
open Obc_utils
open Clocks
open Obc_mapfold

let fuse_blocks b1 b2 =
  { b1 with b_locals = b1.b_locals @ b2.b_locals;
      b_body = b1.b_body @ b2.b_body }

let rec find c = function
  | []    -> raise Not_found
  | (c1, s1) :: h  ->
      if c = c1 then s1, h else let s, h = find c h in s, (c1, s1) :: h

let is_deadcode = function
    | Aassgn (lhs, e) ->
        (match e.e_desc with
           | Eextvalue w ->
             let w' = ext_value_of_pattern lhs in
             w = w' (* TODO: proper compare *)
           | _ -> false
        )
    | Acase (_, []) -> true
    | Afor(_, _, _, { b_body = [] }) -> true
    | _ -> false

let rec joinlist l =
  let l = List.filter (fun a -> not (is_deadcode a)) l in
    match l with
      | [] -> []
      | [s1] -> [s1]
      | s1::s2::l ->
          match s1, s2 with
            | Acase(e1, h1),
              Acase(e2, h2) when e1.e_desc = e2.e_desc ->
                joinlist ((Acase(e1, joinhandlers h1 h2))::l)
            | s1, s2 -> s1::(joinlist (s2::l))

and join_block b =
  { b with b_body = joinlist b.b_body }

and joinhandlers h1 h2 =
  match h1 with
    | [] -> h2
    | (c1, s1) :: h1' ->
        let s1', h2' =
          try let s2, h2'' = find c1 h2 in fuse_blocks s1 s2, h2''
          with Not_found -> s1, h2 in
        (c1, join_block s1') :: joinhandlers h1' h2'

let block funs acc b =
  { b with b_body = joinlist b.b_body }, acc

let program p =
  let p, _ = program_it { defaults with block = block } () p in
  p
