(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* control optimisation *)

(* $Id$ *)

open Minils
open Ident
open Misc
open Obc

let var_from_name map x =
  begin try
    Env.find x map
  with
      _ -> assert false
  end

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
          control map ck (Acase(mk_exp (Elhs x), [(c, [s])]))

let is_deadcode = function
    | Aassgn (lhs, e) ->
        (match e.e_desc with
           | Elhs l -> l = lhs
           | _ -> false
        )
    | Acase (e, []) -> true
    | Afor(_, _, _, []) -> true
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

and joinhandlers h1 h2 =
  match h1 with
    | [] -> h2
    | (c1, s1) :: h1' ->
        let s1', h2' =
          try let s2, h2'' = find c1 h2 in s1@s2, h2''
          with Not_found -> s1, h2 in
        (c1, joinlist s1') :: joinhandlers h1' h2'
