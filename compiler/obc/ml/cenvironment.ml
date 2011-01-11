(**************************************************************************)
(*                                                                        *)
(*  Lucid Synchrone                                                       *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* $Id: cenvironment.ml,v 1.1 2006-03-18 08:04:25 pouzet Exp $ *)

open Misc
open Declarative

(** Environment with static link **)
type cblock =
    { c_block: block;  (* table of free names *)
      c_state: name;   (* the name of the internal state *)
      c_write: name;   (* temporary values *)
    }
type env = cblock list
let empty_env = []
let current env = List.hd env
let cblock env = (current env).c_block
let statename env = (current env).c_state

let push_block block env =
  { c_block = block;
    c_state = symbol#name;
    c_write = symbol#name } :: env
let push block env =
  if env = empty_env
  then push_block block env
  else let cblock = current env in
  { cblock with c_block = block } :: env
let rec findall env i =
  match env with
    [] -> raise Not_found
  | { c_block = b; c_state = st; c_write = wt } :: env ->
      try
  Hashtbl.find b.b_env i, st, wt
      with
  Not_found -> findall env i
let find env i =
  let id, _, _ = findall env i in
  id
