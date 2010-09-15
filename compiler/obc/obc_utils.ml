(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Names
open Misc
open Types
open Obc
open Obc_mapfold
open Global_mapfold

module Deps =
struct

  let deps_longname deps { qual = modn; } = S.add modn deps

  let deps_static_exp_desc funs deps sedesc =
    let (sedesc, deps) = Global_mapfold.static_exp_desc funs deps sedesc in
    match sedesc with
      | Svar ln -> (sedesc, deps_longname deps ln)
      | Sconstructor ln -> (sedesc, deps_longname deps ln)
      | Srecord fnel ->
        let add deps (ln, _) = deps_longname deps ln in
        (sedesc, List.fold_left add deps fnel)
      | Sop (ln, _) -> (sedesc, deps_longname deps ln)
      | _ -> raise Errors.Fallback

  let deps_lhsdesc funs deps ldesc =
    let (ldesc, deps) = Obc_mapfold.lhsdesc funs deps ldesc in
    match ldesc with
      | Lfield (_, ln) -> (ldesc, deps_longname deps ln)
      | _ -> raise Errors.Fallback

  let deps_edesc funs deps edesc =
    let (edesc, deps) = Obc_mapfold.edesc funs deps edesc in
    match edesc with
      | Eop (ln, _) -> (edesc, deps_longname deps ln)
      | Estruct (ln, fnel) ->
        let add deps (ln, _) = deps_longname deps ln in
        (edesc, List.fold_left add (deps_longname deps ln) fnel)
      | _ -> raise Errors.Fallback

  let deps_act funs deps act =
    let (act, deps) = Obc_mapfold.act funs deps act in
    match act with
      | Acase (_, cbl) ->
        let add deps (ln, _) = deps_longname deps ln in
        (act, List.fold_left add deps cbl)
      | _ -> raise Errors.Fallback

  let deps_obj_dec funs deps od =
    let (od, deps) = Obc_mapfold.obj_dec funs deps od in
    (od, deps_longname deps od.o_class)

  let deps_program p =
    let funs = { Obc_mapfold.defaults with
      global_funs = { Global_mapfold.defaults with
                        static_exp_desc = deps_static_exp_desc; };
      lhsdesc = deps_lhsdesc;
      edesc = deps_edesc;
      act = deps_act;
      obj_dec = deps_obj_dec;
    } in
    let (_, deps) = Obc_mapfold.program funs S.empty p in
    S.remove p.p_modname (S.remove "Pervasives" deps)
end
