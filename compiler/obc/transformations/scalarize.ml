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

(** Remove implicit array's deep copy. If ever some p = e with p of type array still exist,
    they are only used as reference to the array, no copy is implied :
    array assignation after [scalarize] is pointer wise assignation *)

(** Scalarize the code : any equation t = e with e_ty an array
    is transformed into : t_ref = e; for i do t[i] = t_ref[i].
    This pass assumes that the backend when encountering t_ref = (e : int^n) will NOT COPY the array
    but set a reference to it. That's why it is declared as an alias.
    No t_ref is created if e was an extended value, no calculation is done, so it can be duplicated.
*)

(** Note that Minils gives few opportunities to [Scalarize]
    Eop with a unique return value or Earray :
    fun pix_2(x :int^3) = (o :int^3^2) let o = [x,x] tel
    fun pix2(x :int^3) = () var o : pixel^2; let o = pix_2(x); tel

    The latter is a special Acall
*)


open Obc
open Obc_utils
open Obc_mapfold


let fresh_for = fresh_for "scalarize"

let act funs () a = match a with
  | Aassgn (p, e) ->
      (match Modules.unalias_type e.e_ty with
        | Types.Tarray (t, size) ->
            let new_vd, new_eq, w_from_e = match e.e_desc with
              | Eextvalue w -> [], [], w
              | _ ->
              (* a reference (alias) to the array, since we have a full expression *)
                  let array_ref = Idents.gen_var "scalarize" "a_ref" in
                  let vd_array_ref = mk_var_dec ~alias: true array_ref e.e_ty in
                  (* reference initialization *)
                  let pat_array_ref = mk_pattern ~loc: e.e_loc e.e_ty (Lvar array_ref) in
                  let init_array_ref = Aassgn (pat_array_ref, e) in
                  [vd_array_ref], [init_array_ref], ext_value_of_pattern pat_array_ref
            in
            (* the copy loop with index [i] *)
            let array_ref_i i = mk_ext_value_exp t (Warray (w_from_e, i)) in
            let p_i i = mk_pattern t (Larray (p, i)) in
            let copy_i i =
              (* recursive call to deal with multidimensional arrays *)
              let a = Aassgn (p_i i, array_ref_i i) in
              let a, _ = act_it funs () a in
              [a]
            in
            let copy_array = fresh_for (mk_exp_const_int 0) (mk_exp_static_int size) copy_i in
            (* resulting act *)
            (match new_vd, new_eq with
              | [],[] ->
                  copy_array, ()
              | _ ->
                  let block = mk_block ~locals: new_vd (new_eq @ [copy_array]) in
                  Ablock block, ()
            )
        | _ -> raise Errors.Fallback
      )
  | _ -> raise Errors.Fallback

let program p =
  let p, _ = program_it { defaults with act = act } () p in
  p
