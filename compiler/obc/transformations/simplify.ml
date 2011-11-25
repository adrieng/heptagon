(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(** This module simplify static expression of the program and deal with :
    (0^n)[3] ==> 0
    [3,4,5][2] ==> 5
 *)



open Names
open Types
open Static
open Obc
open Obc_mapfold

let extvaluedesc funs acc evd = match evd with
  | Warray (ev,e) ->
      let ev, acc = extvalue_it funs acc ev in
      (match ev.w_desc with
        | Wconst se ->
          let se = simplify QualEnv.empty se in
          (match se.se_desc with
            | Sarray_power (sv, [_]) ->
              Wconst sv, acc
            | Sarray_power (sv, _::idx) ->
              Wconst { se with se_desc = Sarray_power (sv, idx)}, acc
            | Sarray sv_l ->
              (match e.e_desc with
                | Eextvalue { w_desc = Wconst i } ->
                  (try
                     let indice = int_of_static_exp QualEnv.empty i in
                     Wconst (Misc.nth_of_list (indice+1) sv_l), acc
                   with _ -> raise Errors.Fallback)
                | _ -> raise Errors.Fallback
              )
            | _ -> raise Errors.Fallback
          )
        | _ -> raise Errors.Fallback
      )
  | _ -> raise Errors.Fallback

let program p =
  let funs = { defaults with evdesc = extvaluedesc } in
  let p, _ = program_it funs [] p in
  p

