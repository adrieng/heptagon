(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* removing reset statements *)

(* REQUIRES automaton switch stateful present *)

open Misc
open Idents
open Heptagon
open Hept_utils
open Types
open Initial

(* We introduce an initialization variable for each reset block  *)
(* e1 -> e2 is translated into if (true fby false) then e1 else e2 *)



let fresh = Idents.gen_fresh "reset" (fun () -> "r")

(* get e and return r, var_dec_r, r = e *)
let bool_var_from_exp e =
  let r = fresh() in
  { e with e_desc = Evar r }, mk_var_dec r (Tid Initial.pbool), mk_equation (Eeq(Evarpat r, e))

(** Merge two reset conditions *)
let merge_resets res1 res2 =
  let mk_or e1 e2 = mk_op_app (Efun Initial.por) [e1;e2] in
  match res1, res2 with
    | None, _ -> res2
    | _, None -> res1
    | Some e1, Some e2 -> Some { e1 with e_desc = mk_or e1 e2 }


(** if res then e2 else e3 *)
let ifres res e2 e3 =
  let init loc = mk_exp (Epre (Some (mk_static_bool true), dfalse)) ~loc:loc (Tid Initial.pbool) in
  match res with
    | None -> mk_op_app Eifthenelse [init e3.e_loc; e2; e3]
    | Some re -> mk_op_app Eifthenelse [re; e2; e3]

(** Keep when ever possible the initialization value *)
let default e =
  match e.e_desc with
    | Econst c -> Some c
    | _ -> None


let edesc funs (res,stateful) ed =
  let ed, _ = Hept_mapfold.edesc funs (res,stateful) ed in
  let ed = match ed with
    | Efby (e1, e2) ->
        (match res, e1 with
         | None, { e_desc = Econst c } ->
            (* no reset : [if res] useless, the initialization is sufficient *)
            Epre(Some c, e2)
         | _ -> ifres res e1 { e2 with e_desc = Epre(default e1, e2) })
    | Eapp({ a_op = Earrow }, [e1;e2], _) ->
        ifres res e1 e2
    | Eapp({ a_op = Enode _ } as op, e_list, re) ->
        Eapp(op, e_list, merge_resets res re)
    | Eiterator(it, ({ a_op = Enode _ } as op), n, pe_list, e_list, re) ->
        Eiterator(it, op, n, pe_list, e_list, merge_resets res re)
    | _ -> ed
  in
    ed, (res,stateful)


(* do nothing when not stateful *)
let eq funs (res,_) eq =
  Hept_mapfold.eq funs (res,eq.eq_stateful) eq

(* do nothing when not stateful *)
let block funs (res,_) b =
  Hept_mapfold.block funs (res,b.b_stateful) b

(* Transform reset blocks in blocks with reseted exps,
   create a var to store the reset condition evaluation. *)
let eqdesc funs (res,stateful) = function
  | Ereset(b, e) ->
      if stateful then (
        let e, _ = Hept_mapfold.exp_it funs (res,stateful) e in
        let e, vd, eq = bool_var_from_exp e in
        let r = merge_resets res (Some e) in
        let b, _ = Hept_mapfold.block_it funs (r,stateful) b in
        let b = { b with b_equs = eq::b.b_equs; b_local = vd::b.b_local; b_stateful = true } in
        Eblock(b), (res,stateful))
      else ( (* recursive call to remove useless resets *)
        let b, _ = Hept_mapfold.block_it funs (res,stateful) b in
        Eblock(b), (res,stateful))
  | Eautomaton _ | Epresent _ ->
      Format.eprintf "[reset] should be done after [automaton present]";
      assert false
  | _ -> raise Errors.Fallback


let funs = { Hept_mapfold.defaults with Hept_mapfold.eq = eq;
                                        Hept_mapfold.block = block;
                                        Hept_mapfold.eqdesc = eqdesc;
                                        Hept_mapfold.edesc = edesc }

let program p =
  let p, _ = Hept_mapfold.program_it funs (None,true) p in
  p
