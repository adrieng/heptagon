(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* Checks that a node declared stateless is stateless *)
open Names
open Location
open Signature
open Modules
open Heptagon
open Hept_mapfold

type error =
  | Eshould_be_a_node
  | Eexp_should_be_stateless

let message loc kind =
  begin match kind with
    | Eshould_be_a_node ->
        Format.eprintf "%aThis node is statefull \
                       but was declared stateless.@."
          print_location loc
    | Eexp_should_be_stateless ->
        Format.eprintf "%aThis expression should be stateless.@."
          print_location loc
  end;
  raise Errors.Error

(** @returns whether the exp is statefull. Replaces node calls with
    the correct Efun or Enode depending on the node signature. *)
let edesc funs statefull ed =
  (* do the recursion on function args *)
  let ed, statefull = Hept_mapfold.edesc funs statefull ed in
    match ed with
      | Efby _ | Epre _ -> ed, true
      | Eapp({ a_op = Earrow }, _, _) -> ed, true
      | Eapp({ a_op = (Enode f | Efun f) } as app, e_list, r) ->
          let ty_desc = find_value f in
          let op = if ty_desc.node_statefull then Enode f else Efun f in
            Eapp({ app with a_op = op }, e_list, r),
          ty_desc.node_statefull or statefull
      | _ -> ed, statefull

let eq funs acc eq =
  let eq, statefull = Hept_mapfold.eq funs acc eq in
    { eq with eq_statefull = statefull }, statefull

let block funs acc b =
  let b, statefull = Hept_mapfold.block funs false b in
    { b with b_statefull = statefull }, acc or statefull

let escape_unless funs acc esc =
  let esc, statefull = Hept_mapfold.escape funs false esc in
    if statefull then
      message esc.e_cond.e_loc Eexp_should_be_stateless;
    esc, acc or statefull

let present_handler funs acc ph =
  let p_cond, statefull = Hept_mapfold.exp_it funs false ph.p_cond in
    if statefull then
      message ph.p_cond.e_loc Eexp_should_be_stateless;
  let p_block, acc = Hept_mapfold.block_it funs acc ph.p_block in
    { ph with p_cond = p_cond; p_block = p_block }, acc

let node_dec funs _ n =
  Idents.enter_node n.n_name;
  let n, statefull = Hept_mapfold.node_dec funs false n in
    if statefull & not (n.n_statefull) then
      message n.n_loc Eshould_be_a_node;
    n, false

let program p =
  let funs =
    { Hept_mapfold.defaults with edesc = edesc;
        escape_unless = escape_unless;
        present_handler = present_handler;
        eq = eq; block = block; node_dec = node_dec } in
  let p, _ = Hept_mapfold.program_it funs false p in
    p
