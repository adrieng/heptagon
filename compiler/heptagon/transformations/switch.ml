(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

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
      var ck, x_up, x_down, y_up, y_down in
      x_up, x_down = split ck x
      ck = e
      block_up[x_up /x][y_up /y]
      block_down[x_down /x][y_down /y]
      y = merge ck (up -> y_up) (down -> y_down)
    }
*)

(* e_level_ck is used to have correct behavior for side effects :
   it keeps track of the fact that a call
   without interaction with the dataflow was in a case of the switch *)




open Misc
open Heptagon
open Hept_utils
open Hept_mapfold

(** [fresh_case_var name constructor] returns a fresh var with name [name_constr] *)
let fresh_case_var name constr =
  let tmp (n,c) =
    false, n^"_"^(Names.print_pp_to_name Global_printer.print_qualname c)
  in
  Idents.gen_fresh "switch" tmp (name,constr)

let fresh_clock_id () =
  Idents.gen_var "switch" "ck"

(** Renaming environment [h]


    to rename the shared variables : x = ... ==> x_up = ... *)
module Rename = struct
include Idents.Env

let rename n h =
  try find n h with Not_found -> n


(* forget old substitutions, and set new ones for [defnames] *)
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
    let vd_nn = mk_var_dec nn orig_vd.v_type orig_vd.v_linearity in
    vd_nn::locals, Idents.Env.add vd_nn.v_ident vd_nn vd_env
  in
    fold add_one h (locals, vd_env)
end


(** Environment [env]
    used to sample the shared variables : x ==> x when Up(ck)... *)
module Env = struct


open Idents
open Names
open Clocks

type vd_clock_tree =
  | Base of var_dec Idents.Env.t
  | Level of ck * var_dec Idents.Env.t * vd_clock_tree

type t = ident Rename.t * vd_clock_tree
  (** (h, used, vdtree) [h] is the substitution env *)

let level_up constr ckid defnames (h,vdt) =
  let h' = Rename.level_up defnames constr h in
  match vdt with
  | Base _ -> (h', Level(Con(Cbase, constr, ckid), Idents.Env.empty, vdt))
  | Level (ck, _,_) -> (h', Level(Con(ck, constr, ckid), Idents.Env.empty, vdt))

(*
let level_down env = match env with
  | Base -> Format.eprintf "Internal Error : wrong switch level"; assert false
  | Level(_,_, env_down) -> env_down *)

let add_vd vd (h,vdt) = match vdt with
  | Base vds ->
      (h, Base (Idents.Env.add vd.v_ident vd vds))
  | Level (ck, vds, ed) ->
      (h, Level(ck, Idents.Env.add vd.v_ident vd vds, ed))

let rec _get_vd v vdt = match vdt with
  | Base vds -> Idents.Env.find v vds
  | Level (_,vds, vdt) ->
      try Idents.Env.find v vds
      with Not_found -> _get_vd v vdt

let get_vd v (h,vdt) = _get_vd v vdt

(** return a new name for ident [v] *)
let new_name v vdt =
  let rec _nn n vdt = match vdt with
    | Base _ -> n
    | Level (Con(_,constr,_),_,vdt)->
        (_nn n vdt)^"_"^(Names.print_pp_to_name Global_printer.print_qualname constr)
    | Level _ -> Misc.internal_error "Level should always have a Con"
  in
  _nn (Idents.name v) vdt



(** returns wether it is a new used name, the accordingly updated env and the substitution name *)
let rename v (h, vdt) = match vdt with
  | Base vds
  | Level (_, vds, _) ->
      if Idents.Env.mem v vds
      then (* it is a local variable, no renaming is needed *)
        false, (h, vdt), v
      else begin (* it is a shared variable *)
        try
          false, (h, vdt), Rename.find v h (* it is already in the subst *)
        with Not_found -> (* it is a new used variable *)
          let new_n = new_name v vdt in
          let new_v = Idents.gen_var "switch" ~reset:(Idents.is_reset v) new_n in
          let h = Rename.add v new_v h in
          true, (h, vdt), new_v
      end

let update_locals locals (h,vdt) =
  let add_one n nn locals =
    let orig_vd = _get_vd n vdt in
    let vd_nn = mk_var_dec nn orig_vd.v_type orig_vd.v_linearity in
    vd_nn::locals
  in
  Idents.Env.fold add_one h locals


(** Gives back the current level clock *)
let current_level (_,vdt) = match vdt with
  | Base _ -> Cbase
  | Level (ck, _,_) -> ck

(** Set the base clock of an expression to the current level of the [env] *)
let annot_exp e env =
  { e with e_level_ck = current_level env }

let empty =  (Rename.empty, Base Idents.Env.empty)

end



(** Mapfold *)

let rename x (used,env) =
  let new_used, env, x' = Env.rename x env in
  if new_used
  then x', (Idents.IdentSet.add x used, env)
  else x', (used, env)


(* apply the renaming for shared defined variables *)
let pattern _ uenv pat = match pat with
    | Evarpat x ->
        let x, uenv = rename x uenv in
        Evarpat x, uenv
    | _ -> raise Errors.Fallback

(* Update vd_env, the environment used to remember the vds of original variables *)
let var_dec _ (used, env) vd =
  let env = Env.add_vd vd env in
  vd, (used,env)

(* apply the renaming to the defnames *)
let block funs uenv b =
  let rename_defnames defnames uenv =
    Idents.Env.fold
      (fun n vd (uenv, defnames) ->
          let n, uenv = rename n uenv in
          uenv, Idents.Env.add n { vd with v_ident = n } defnames)
      defnames (uenv, Idents.Env.empty)
  in
  let uenv, defnames = rename_defnames b.b_defnames uenv in
  let b = { b with b_defnames = defnames } in
  Hept_mapfold.block funs uenv b

(* apply the sampling on shared vars *)
let exp funs (used,env) e =
  let e = Env.annot_exp e env in
  Hept_mapfold.exp funs (used,env) e

let edesc _ uenv ed = match ed with
  | Evar x ->
      let x, uenv = rename x uenv in
      Evar x, uenv
  | _ -> raise Errors.Fallback

(* update stateful and loc *)
let eq funs uenv eq =
  let eq, uenv = Hept_mapfold.eq funs uenv eq in
  let eqd = match eq.eq_desc with
    | Eblock b -> (* probably created by eqdesc, so update stateful and loc *)
        Eblock { b with b_stateful = eq.eq_stateful; b_loc = eq.eq_loc }
    | _ -> eq.eq_desc in
  { eq with eq_desc = eqd }, uenv


(* remove the Eswitch *)
let eqdesc funs (used, env) eqd = match eqd with
  | Eswitch (e, sw_h_l) ->

      (* Recursive call only on [e] since the handlers need new environments. *)
      let e, (used,env) = exp_it funs (used,env) e in

      (* create, if needed, a clock var corresponding to the switch condition [e] *)
      let ck, locals, equs = match e.e_desc with
        | Evar x -> x, [], []
        | _ ->
            let ck = fresh_clock_id () in
            let locals = [mk_var_dec ck e.e_ty e.e_linearity] in
            let equs = [mk_equation (Eeq (Evarpat ck, e))] in
            ck, locals, equs
      in

      (* typing have proved that defined variables are the same among states *)
      (* They are updated after eqdesc is done in [eq] *)
      let defnames = (List.hd sw_h_l).w_block.b_defnames in


      let (c_env_l, locals, equs, used) =
        (* deal with the handlers, return the list of pair of constructor, associated environment *)
        let switch_handler (c_env_l, locals, equs, used) sw_h =
          let constr = sw_h.w_name in
          (* level up *)
          let env = Env.level_up constr ck defnames env in
          (* mapfold inside block *)
          let b_eq, (used,env) = block_it funs (used,env) sw_h.w_block in
          (* inline the handler as a block *)
          let equs = (mk_equation (Eblock b_eq))::equs in
          (* add to the locals the needed vars *)
          let locals = Env.update_locals locals env in
          ((constr,env)::c_env_l, locals, equs, used)
        in
        (* fold over used in order to collect all the used vars *)
        List.fold_left switch_handler ([], locals, equs, used) sw_h_l
      in


      let equs =
        (* create a merge equation for each defnames *)
        let new_merge n vd equs =
          let c_env_to_c_e (constr,env) =
            let new_n,_, n = Env.rename n env in
            (* rename should not change the env since we deal with defnames *)
            assert (not new_n);
            constr, mk_exp (Evar n) vd.v_type ~linearity:vd.v_linearity
          in
          let c_e_l = List.map c_env_to_c_e c_env_l in
          let merge = mk_exp (Emerge (ck, c_e_l)) vd.v_type ~linearity:vd.v_linearity in
          let new_n, _, n = Env.rename n env in
          (* rename should not change the env since we deal with defnames *)
          assert (not new_n);
          (mk_equation (Eeq (Evarpat n, merge)))::equs
        in
        Idents.Env.fold new_merge defnames equs
      in

      let (uenv,equs) =
        (* create a split equation for each used names *)
        let new_split n ((used,env), equs) =
          (* fold over used in order to collect all the used vars *)
          (*let c_env_to_pat (c,cenv) (used, (n_list,c_l)) =
            let n, (used,cenv) = rename n (used,cenv) in
            (used, ((Evarpat n)::n_list, c::c_l))
          in
          let used, (pat, c_l) = List.fold_right c_env_to_pat c_env_l (used,([],[])) in
          *)
          let c_env_to_pat (c,cenv) (n_list,c_l) =
            let _,_,n = Env.rename n cenv in
            ((Evarpat n)::n_list, c::c_l)
          in
          let (pat, c_l) = List.fold_right c_env_to_pat c_env_l ([],[]) in
          let vd = Env.get_vd n env in
          let n, (used,env) = rename n (used,env) in
          let v = mk_exp (Evar n) vd.v_type ~linearity:vd.v_linearity in
          let v_t = Signature.prod (repeat_list vd.v_type (List.length c_l)) in
          let v_lt = Linearity.prod (repeat_list vd.v_linearity (List.length c_l)) in
          let split = mk_exp (Esplit (ck, c_l, v)) v_t ~linearity:v_lt in
          ((used,env), (mk_equation (Eeq (Etuplepat pat, split)))::equs)
        in
        (* update the environment, but deal with [used] from the handlers *)
        Idents.IdentSet.fold new_split used ((used,env),equs)
      in

        (* return the transformation in a block *)
      let b = mk_block ~defnames:defnames ~locals:locals equs in
      Eblock b, uenv
  | _ -> raise Errors.Fallback

let program p =
  let funs = { Hept_mapfold.defaults
               with pat = pattern; var_dec = var_dec; block = block;
                    exp = exp; edesc = edesc; eq = eq; eqdesc = eqdesc } in
  let p, _ = program_it funs (Idents.IdentSet.empty,Env.empty) p in
    p





