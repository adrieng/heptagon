(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(** Remove implicit array's deep copy. If ever some p = e with p of type array still exist,
  they are only used as reference to the array, no copy is implied :
  array assignation after [scalarize] is pointer wise assignation *)


open Misc
open Obc
open Obc_utils
open Obc_mapfold

let fresh_for = fresh_for "scalarize"

let act funs () a = match a with
  | Aassgn (p,e) ->
      (match e.e_ty with
        | Types.Tarray (t, size) -> (* TODO ayayayaye *)
          (* a reference (alias) to the array, since we could have a full expression *)
          let array_ref = Idents.gen_var "scalarize" "a_ref" in
          let vd_array_ref = mk_var_dec array_ref (Types.Tmutable p.pat_ty) in
          (* reference initialization *)
          let pat_array_ref = mk_pattern ~loc:e.e_loc p.pat_ty (Lvar array_ref) in
          let init_array_ref = Aassgn (pat_array_ref, e) in
          (* the copy loop *)
          let array_ref_i i = mk_pattern_exp t (Larray (pat_array_ref, i)) in
          let p_i i = mk_pattern t (Larray (p, i)) in
          let copy_i i =
            (* recursive call to deal with multidimensional arrays (go deeper) *)
            let a = Aassgn (p_i i, array_ref_i i) in
            let a, _ = act_it funs () a in
            [a]
          in
          let copy_array = fresh_for size copy_i in
          (* resulting block *)
          let block = mk_block ~locals:[vd_array_ref] [init_array_ref; copy_array] in
          Ablock block, ()
        | _ -> raise Errors.Fallback
      )
  | _ -> raise Errors.Fallback


let program p =
  let p, _ = program_it { defaults with act = act } () p in
  p


