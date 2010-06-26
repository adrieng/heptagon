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
        let e = var_from_name map n in
        control map ck (Obc.Case(Obc.Lhs e, [(c, s)]))

let rec simplify act =
  match act with
    | Obc.Assgn (lhs, e) ->
        (match e with
           | Obc.Lhs l when l = lhs -> Obc.Nothing
           | _ -> act
        )
    | Obc.Case(lhs, h) ->
        (match simplify_handlers h with
           | [] -> Obc.Nothing
           | h -> Obc.Case(lhs, h)
        )
    | _ -> act

and simplify_handlers = function
  | [] -> []
  | (n,a)::h ->
      let h = simplify_handlers h in
      (match simplify a with
         | Obc.Nothing -> h
         | a -> (n,a)::h
      )

let rec join s1 s2 =
  match simplify s1, simplify s2 with
    | Obc.Case(Obc.Lhs(n), h1), Obc.Case(Obc.Lhs(m), h2) when n = m ->
        Obc.Case(Obc.Lhs(n), joinhandlers h1 h2)
    | s1, Obc.Nothing -> s1
    | Obc.Nothing, s2 -> s2
    | s1, Obc.Comp(s2, s3) -> Obc.Comp(join s1 s2, s3)
    | s1, s2 -> Obc.Comp(s1, s2)

and joinhandlers h1 h2 =
  match h1 with
    | [] -> h2
    | (c1, s1) :: h1' ->
        let s1', h2' =
          try let s2, h2'' = find c1 h2 in join s1 s2, h2''
          with Not_found -> simplify s1, h2 in
        (c1, s1') :: joinhandlers h1' h2'

let rec joinlist = function
  | []      -> Obc.Nothing
  | s :: l  -> join s (joinlist l)
