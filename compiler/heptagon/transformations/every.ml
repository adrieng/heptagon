open Heptagon


(* Transform [f (...) every e]
   into [f (...) every r] and add an equation [r=e] *)

let is_var = function
  | { e_desc = Evar _ } -> true
  | _ -> false

let block funs acc b =
  let b, (v, acc_eq_list) = Hept_mapfold.block funs ([], []) b in
    { b with b_local = v @ b.b_local; b_equs = acc_eq_list@b.b_equs }, acc

let edesc funs (v,acc_eq_list) ed =
  let ed, (v, acc_eq_list) = Hept_mapfold.edesc funs (v,acc_eq_list) ed in
  match ed with
    | Eapp (op, e_list, Some re) when not (is_var re) ->
        let re, vre, eqre = Reset.bool_var_from_exp re in
        Eapp(op, e_list, Some re), (vre::v, eqre::acc_eq_list)
    | Eiterator(it, op, n, pe_list, e_list, Some re) when not (is_var re) ->
        let re, vre, eqre = Reset.bool_var_from_exp re in
          Eiterator(it, op, n, pe_list, e_list, Some re),
             (vre::v, eqre::acc_eq_list)
    | _ -> ed, (v, acc_eq_list)

let program p =
  let funs = { Hept_mapfold.defaults
               with Hept_mapfold.edesc = edesc; Hept_mapfold.block = block } in
  let p, _ = Hept_mapfold.program_it funs ([],[]) p in
    p
