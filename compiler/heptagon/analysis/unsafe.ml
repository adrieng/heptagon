(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* Checks that a node not declared unsafe is safe, and set app unsafe flag. *)
open Names
open Location
open Signature
open Modules
open Heptagon
open Hept_mapfold

type error =
  | Eshould_be_unsafe

let message loc kind =
  begin match kind with
    | Eshould_be_unsafe ->
        Format.eprintf "%aThis exp is unsafe but the current node is not declared unsafe.@."
          print_location loc
  end;
  raise Errors.Error

(* Returns whether an op is unsafe *)
let unsafe_op op = match op with
  | Enode f | Efun f ->
      (find_value f).node_unsafe
  | _ -> (*TODO il y a des op unsafe ??*)
      false

(* Update app unsafe field
   and gives an error if some exp is unsafe in a safe node ([unsafe]=false) *)
let exp funs unsafe e =
  let e, unsafe = Hept_mapfold.exp funs unsafe e in
    match e.e_desc with
      | Eapp({ a_op = op } as app, e_l, r) ->
          let u = (unsafe_op op) or app.a_unsafe in
          if u & (not unsafe)
          then message e.e_loc Eshould_be_unsafe
          else {e with e_desc = Eapp({ app with a_unsafe = u }, e_l, r)}, (unsafe or u)
      | Eiterator(it, ({ a_op = op } as app), n, pe_list, e_list, r) ->
          let u = (unsafe_op op) or app.a_unsafe in
          if u & (not unsafe)
          then message e.e_loc Eshould_be_unsafe
          else
            {e with e_desc = Eiterator(it, { app with a_unsafe = u }, n, pe_list, e_list, r)}
            , (unsafe or u)
      | _ -> e, unsafe

(* unsafe nodes are rejected if they are not declared unsafe *)
let node_dec funs _ n = Hept_mapfold.node_dec funs n.n_unsafe n

let funs =
  { Hept_mapfold.defaults with
      exp = exp;
      node_dec = node_dec; }

let program p =
  let p, _ = Hept_mapfold.program_it funs false p in
  p
