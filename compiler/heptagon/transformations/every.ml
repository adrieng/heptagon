open Heptagon
open Hept_mapfold
open Types


(* Transform [f (...) every e]
   into [f (...) every r] and add an equation [r=e] *)

let mk_bool_var n = mk_exp (Evar n) (Tid Initial.pbool)
let mk_bool_param n = mk_var_dec n (Tid Initial.pbool)

let fresh = Idents.gen_fresh "reset" (fun () -> "r")
(* add an equation *)
let equation v acc_eq_list e =
  let n = fresh() in
  n,
  (mk_bool_param n) :: v,
  (mk_equation (Eeq(Evarpat n, e))) ::acc_eq_list


let statefull eq_list = List.exists (fun eq -> eq.eq_statefull) eq_list

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
        let n, v, acc_eq_list = equation v acc_eq_list re in
        let re = { re with e_desc = Evar n } in
          Eapp(op, e_list, Some re), (v, acc_eq_list)

    | Eiterator(it, op, n, e_list, Some re) when not (is_var re) ->
        let x, v, acc_eq_list = equation v acc_eq_list re in
        let re = { re with e_desc = Evar x } in
          Eiterator(it, op, n, e_list, Some re), (v, acc_eq_list)

    | _ -> ed, (v, acc_eq_list)

let program p =
  let funs = { Hept_mapfold.defaults
               with edesc = edesc; block = block } in
  let p, _ = program_it funs ([],[]) p in
    p
