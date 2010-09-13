(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* control optimisation *)


open Minils
open Idents
open Misc
open Obc
open Clocks

let var_from_name map x =
  begin try
    Env.find x map
  with
      _ -> assert false
  end

let fuse_blocks b1 b2 =
  { b1 with b_locals = b1.b_locals @ b2.b_locals;
      b_body = b1.b_body @ b2.b_body }

let rec find c = function
  | []    -> raise Not_found
  | (c1, s1) :: h  ->
      if c = c1 then s1, h else let s, h = find c h in s, (c1, s1) :: h

let rec control map ck s =
  match ck with
    | Cbase | Cvar { contents = Cindex _ } -> s
    | Cvar { contents = Clink ck } -> control map ck s
    | Con(ck, c, n)  ->
        let x = var_from_name map n in
          control map ck (Acase(mk_exp (Elhs x), [(c, mk_block [s])]))

let is_deadcode = function
    | Aassgn (lhs, e) ->
        (match e.e_desc with
           | Elhs l -> l = lhs
           | _ -> false
        )
    | Acase (e, []) -> true
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
