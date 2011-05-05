(****************************************************)
(*                                                  *)
(*  Heptagon/BZR                                    *)
(*                                                  *)
(*  Author : Gwenaël Delaval                        *)
(*  Organization : INRIA Rennes, VerTeCs            *)
(*                                                  *)
(****************************************************)

(* 
   Translate enumerated types (state variables) into boolean

   type t = A | B | C | D

   A --> 00
   B --> 01
   C --> 10
   D --> 11

   x : t --> x1,x2 : bool

   (e when A(x))
   -->
   (e when False(x1)) when False(x2)
   
   merge x (A -> e0) (B -> e1) (C -> e2) (D -> e3)
   -->
   merge x1 (False -> merge x2 (False -> e0) (True -> e1))
            (True  -> merge x2 (False -> e2) (True -> e3))
*)

(* $Id: boolean.mli 74 2009-03-11 10:21:25Z delaval $ *)

val program : Heptagon.program -> Heptagon.program
