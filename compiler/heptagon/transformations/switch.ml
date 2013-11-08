(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)

(* ASSUMES no automaton, no present, no last, no reset *)

(* Removing switch statements *)

(* sketch of the transformation :
   Eswitch is translated into an Eblock in the following way :

   switch (e)
     up : block_up
     down : block_down

with one defined var y ( defnames = {y} ) and used var x
(example : block_up = block : { var t in  t = x + 3; y = t + 2; }

    becomes :

    block : {
      var ck, y_up, y_down in
      ck = e
      block_up[x when up(ck) /x][y_up /y]
      block_down[x when up(ck) /x][y_down /y]
      y = merge ck (up -> y_up) (down -> y_down)
    }
*)

(* e_level_ck is used to have correct behavior for side effects :
   it keep track of the fact that a call
   without interaction with the dataflow was in a case of the switch *)




open Heptagon
open Hept_utils
open Hept_mapfold

(** Give the var [name] and a [constructor], returns fresh [name_constr] *)
let fresh_case_var name constr =
  let tmp (n,c) =
    n^"_"^(Names.print_pp_to_name Global_printer.print_qualname c) in
  Idents.gen_fresh "switch" tmp (name,constr)

let fresh_clock_id () =
  Idents.gen_var "switch" "ck"



(** Environment [env]
    used to sample the shared variables : x ==> x when Up(ck)... *)
module Env = struct


open Idents
open Clocks

type t = Base | Level of ck * IdentSet.t * t

let level_up constr ckid env = match env with
  | Base -> Level(Con(Cbase, constr, ckid), IdentSet.empty, env)
  | Level (ck, _,_) -> Level(Con(ck, constr, ckid), IdentSet.empty, env)

let level_down env = match env with
  | Base -> Format.eprintf "Internal Error : wrong switch level"; assert false
  | Level(_,_, env_down) -> env_down

let add_var x env = match env with
  | Base -> Base
  | Level (ck, h, ed) ->
      Level(ck, IdentSet.add x h, ed)

(** Wraps [Evar]s with the needed [when]
    corresponding to their definition level *)
let rec sample_var e env = match env with
  | Base -> e
  | Level (Con(_, constr, ck), h, env_d) ->
      (match e.e_desc with
        | Evar x ->
            if IdentSet.mem x h
            then e (* the var is declared at this level, nothing to do *)
            else (*sample to lower level*)
              {e with e_desc =
                Ewhen ((sample_var e env_d), constr, ck)}
        | _ ->
          (Format.eprintf "'sample_var' called on full exp : %a@."
             Hept_printer.print_exp e;
           assert false))
  | Level _ -> assert false


(** Gives back the current level clock *)
let current_level env = match env with
  | Base -> Cbase
  | Level (ck, _,_) -> ck

(** Set the base clock of an expression to the current level of the [env] *)
let annot_exp e env =
  { e with e_level_ck = current_level env }

end

(** Renaming environment [h]
    to rename the defined shared variables : x = ... ==> x_up = ... *)
module Rename = struct
include Idents.Env

let rename n h =
  try find n h with _ -> n

let rename_defnames defnames h =
  fold (fun n ty acc -> add (rename n h) ty acc) defnames empty

let level_up defnames constr h =
  let ident_level_up n new_h =
    let old_n = rename n h in
    let new_n = fresh_case_var (Idents.name old_n) constr in
    add n new_n new_h
  in
  fold (fun n _ new_h -> ident_level_up n new_h) defnames empty

(* only use of [vd_env] is here to create y_Up with the same type as y, etc. *)
let add_to_locals vd_env locals h =
  let add_one n nn (locals,vd_env) =
    let orig_vd = Idents.Env.find n vd_env in
    let vd_nn = mk_var_dec nn orig_vd.v_type ~linearity:orig_vd.v_linearity in
    vd_nn::locals, Idents.Env.add vd_nn.v_ident vd_nn vd_env
  in
    fold add_one h (locals, vd_env)
end

(** Mapfold *)


(* apply the renaming for shared defined variables *)
let pattern _ (vd_env,env,h) pat = match pat with
    | Evarpat x -> Evarpat (Rename.rename x h), (vd_env,env,h)
    | _ -> raise Errors.Fallback

let var_dec _ (vd_env,env,h) vd =
  let env = Env.add_var vd.v_ident env in
  let vd_env = Idents.Env.add vd.v_ident vd vd_env in
  vd, (vd_env,env,h)

(* apply the renaming to the defnames *)
let block funs (vd_env,env,h) b =
  let b = { b with b_defnames = Rename.rename_defnames b.b_defnames h } in
  Hept_mapfold.block funs (vd_env,env,h) b

(* apply the sampling on shared vars *)
let exp funs (vd_env,env,h) e =
  let e = Env.annot_exp e env in
  match e.e_desc with
  | Evar _ -> Env.sample_var e env, (vd_env,env,h)
  | _ -> Hept_mapfold.exp funs (vd_env,env,h) e

(* update stateful and loc *)
let eq funs (vd_env,env,h) eq =
  let eqd = match eq.eq_desc with
    | Eblock b -> (* probably created by eqdesc, so update stateful and loc *)
        Eblock { b with b_stateful = eq.eq_stateful; b_loc = eq.eq_loc }
    | _ -> eq.eq_desc in
  Hept_mapfold.eq funs (vd_env,env,h) {eq with eq_desc = eqd}

(* remove the Eswitch *)
let eqdesc funs (vd_env,env,h) eqd = match eqd with
  | Eswitch (e, sw_h_l) ->
      (* create a clock var corresponding to the switch condition [e] *)
      let ck = fresh_clock_id () in
      let e, (vd_env,env,h) = exp_it funs (vd_env,env,h) e in
      let locals = [mk_var_dec ck e.e_ty ~linearity:e.e_linearity] in
      let equs = [mk_equation (Eeq (Evarpat ck, e))] in

      (* typing have proved that defined variables are the same among states *)
      let defnames = (List.hd sw_h_l).w_block.b_defnames in

      (* deal with the handlers *)
      let switch_handler (c_h_l, locals, equs, vd_env) sw_h =
        let constr = sw_h.w_name in
        (* level up *)
        let h = Rename.level_up defnames constr h in
        let env = Env.level_up constr ck env in
        (* add to the locals the new vars from leveling_up *)
        let locals,vd_env = Rename.add_to_locals vd_env locals h in
        (* mapfold with updated envs *)
        let b_eq, (_,_,h) = block_it funs (vd_env,env,h) sw_h.w_block in
        (* inline the handler as a block *)
        let equs = (mk_equation (Eblock b_eq))::equs in
        ((constr,h)::c_h_l, locals, equs, vd_env)
      in

      let (c_h_l, locals, equs, vd_env) =
        List.fold_left switch_handler ([], locals, equs, vd_env) sw_h_l
      in

      (* create a merge equation for each defnames *)
      let new_merge n vd equs =
        let c_h_to_c_e (constr,h) =
          constr, mk_exp (Evar(Rename.rename n h)) vd.v_type ~linearity:vd.v_linearity
        in
        let c_e_l = List.map c_h_to_c_e c_h_l in
        let merge = mk_exp (Emerge (ck, c_e_l)) vd.v_type ~linearity:vd.v_linearity in
        (mk_equation (Eeq (Evarpat (Rename.rename n h), merge))) :: equs
      in
      let equs =
        Idents.Env.fold (fun n vd equs -> new_merge n vd equs) defnames equs
      in

        (* return the transformation in a block *)
      let b = mk_block ~defnames:defnames ~locals:locals equs in
      Eblock b, (vd_env,env,h)
  | _ -> raise Errors.Fallback

let program p =
  let funs = { Hept_mapfold.defaults
               with pat = pattern; var_dec = var_dec; block = block;
                    exp = exp; eq = eq; eqdesc = eqdesc } in
  let p, _ = program_it funs (Idents.Env.empty,Env.Base,Rename.empty) p in
    p
