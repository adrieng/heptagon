(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* removing reset statements *)


open Misc
open Ident
open Heptagon
open Hept_mapfold
open Types

(* We introduce an initialization variable for each block  *)
(* Using an asynchronous reset would allow to produce      *)
(* better code avoiding to introduce n local variables and *)
(* n state variables                                       *)
(* reset
     switch e with
       case C1 do ...
     | case C2 do ...
     | case C3 do ...
     end
   every r

   switch e with
     case C1 do ... (* l_m1 *)
                m1 = false; m2 = l_m2; m3 = l_m3
   | case C2 do ... (* l_m2 *)
                m1 = l_m1; m2 = false; m3 = l_m3
   | case C3 do ... (* l_m3 *)
                m1 = l_m1; m2 = l_m2; m3 = false
   end;
   l_m1 = if res then true else true fby m1;...;
   l_m3 = if res then true else true fby m3

   e1 -> e2 is translated into if (true fby false) then e1 else e2
*)

let mk_bool_var n =
  mk_exp (Evar n) (Tid Initial.pbool)
let mk_bool_param n =
  mk_var_dec n (Tid Initial.pbool)

let or_op_call = mk_op (Efun Initial.por)

let pre_true e =
  { e with e_desc = Epre (Some (mk_static_exp ~ty:(Tid Initial.pbool)
                              (Sconstructor Initial.ptrue)), e) }
let init e = pre_true { dfalse with e_loc = e.e_loc }

(* the boolean condition for a structural reset *)
type reset =
  | Rfalse
  | Rorthen of reset * ident

let rfalse = Rfalse
let rvar n = Rorthen(Rfalse, n)

let true_reset = function
  | Rfalse -> false
  | _ -> true

let rec or_op res e =
  match res with
    | Rfalse -> e
    | Rorthen(res, n) ->
        or_op res { e with e_desc = Eapp(or_op_call, [mk_bool_var n; e], None) }

let default e =
  match e.e_desc with
    | Econst c -> Some c
    | _ -> None

let exp_of_res res =
  match res with
    | Rfalse -> dfalse
    | Rorthen(res, n) -> or_op res (mk_bool_var n)

let ifres res e2 e3 =
  match res with
    | Rfalse -> mk_op_app Eifthenelse [init e3; e2; e3]
    | _ -> (* a reset occurs *)
        mk_op_app Eifthenelse [exp_of_res res; e2; e3]

(* add an equation *)
let equation v acc_eq_list e =
  let n = Ident.fresh "r" in
  n,
  (mk_bool_param n) :: v,
  (mk_equation (Eeq(Evarpat n, e))) ::acc_eq_list

let orthen v acc_eq_list res e =
  match e.e_desc with
    | Evar(n) -> v, acc_eq_list, Rorthen(res, n)
    | _ ->
        let n, v, acc_eq_list = equation v acc_eq_list e in
        v, acc_eq_list, Rorthen(res, n)

let mk_local_equation i k m lm =
  (* m_i = false; m_j = l_mj *)
  if i = k then
    mk_simple_equation (Evarpat m) dfalse
  else
    mk_simple_equation (Evarpat m) (mk_bool_var lm)

let mk_global_equation res m lm =
  (* [ l_m1 = if res then true else true fby m1;...;
     l_mn = if res then true else true fby mn ] *)
  let e =
    (match res with
       | Rfalse -> pre_true (mk_bool_var m)
       | _ -> mk_exp (ifres res dtrue (pre_true (mk_bool_var m)))
           (Tid Initial.pbool)
    ) in
    mk_simple_equation (Evarpat lm) e

let statefull eq_list = List.exists (fun eq -> eq.eq_statefull) eq_list


let edesc funs (res, v, acc_eq_list) ed =
  let ed, _ = Hept_mapfold.edesc funs (res, v, acc_eq_list) ed in
  let ed = match ed with
    | Efby (e1, e2) ->
        (match res, e1 with
           | Rfalse, { e_desc = Econst c } ->
               (* no reset *)
               Epre(Some c, e2)
           | _ ->
               ifres res e1
                 { e2 with e_desc = Epre(default e1, e2) }
        )
    | Eapp({ a_op = Earrow }, [e1;e2], _) ->
        ifres res e1 e2

    (* add reset to the current reset exp. *)
    | Eapp({ a_op = Enode _ } as op, e_list, Some re) ->
        Eapp(op, e_list, Some (or_op res re))
    (* create a new reset exp if necessary *)
    | Eapp({ a_op = Enode _ } as op, e_list, None) ->
        if true_reset res then
          Eapp(op, e_list, Some (exp_of_res res))
        else
          Eapp(op, e_list, None)
    (* add reset to the current reset exp. *)
    | Eiterator(it, ({ a_op = Enode _ } as op), n, e_list, Some re) ->
        Eiterator(it, op, n, e_list, Some (or_op res re))
    (* create a new reset exp if necessary *)
    | Eiterator(it, ({ a_op = Enode _ } as op), n, e_list, None) ->
        if true_reset res then
          Eiterator(it, op, n, e_list, Some (exp_of_res res))
        else
          Eiterator(it, op, n, e_list, None)
    | _ -> ed
  in
    ed, (res, v, acc_eq_list)

let switch_handlers funs (res, v, acc_eq_list) switch_handlers =
  (* introduce a reset bit for each branch *)
  let m_list = List.map (fun _ -> Ident.fresh "r") switch_handlers in
  let lm_list = List.map (fun _ -> Ident.fresh "r") switch_handlers in

  let body i ({ w_block = b } as sh) m lm =
    let defnames = List.fold_left (fun acc m ->
           Env.add m (Tid Initial.pbool) acc) b.b_defnames m_list in
    let _, (_, v, acc_eq_list) =
      mapfold (eq_it funs) (rvar lm, b.b_local, []) b.b_equs in
    let added_eqs = mapi2 (mk_local_equation i) m_list lm_list in
      { sh with w_block = { b with b_local = v; b_defnames = defnames;
                    b_equs = added_eqs @ acc_eq_list } } in

  let v = (List.map mk_bool_param m_list)@
    (List.map mk_bool_param lm_list)@v in
  let switch_handlers = mapi3 body switch_handlers m_list lm_list in
  let added_eqs = List.map2 (mk_global_equation res) m_list lm_list in

    v, switch_handlers, acc_eq_list @ added_eqs

let eq funs (res, v, acc_eq_list) equ =
  match equ.eq_desc with
    | Eswitch(e, sh) ->
        let e, _ = exp_it funs (res, v, acc_eq_list) e in
        let v, sh, acc_eq_list =
          switch_handlers funs (res, v, acc_eq_list) sh in
        equ, (res, v, { equ with eq_desc = Eswitch(e, sh) } :: acc_eq_list)

    | Ereset(eq_list, e) ->
        let e, _ = exp_it funs (res, v, acc_eq_list) e in
        let v, acc_eq_list, res =
          if statefull eq_list then
            orthen v acc_eq_list res e
          else
            let _, v, acc_eq_list = equation v acc_eq_list e in
              v, acc_eq_list, res
        in
        let _, (res, v, acc_eq_list) =
          mapfold (eq_it funs) (res, v, acc_eq_list) eq_list in
          equ, (res, v, acc_eq_list)

    | _ ->
        let equ, (res, v, acc_eq_list) = eq funs (res, v, acc_eq_list) equ in
          equ, (res, v, equ::acc_eq_list)


let node funs _ n =
  let n, (_, v, eq_list) = Hept_mapfold.node_dec funs (rfalse, [], []) n in
    { n with n_local = v @ n.n_local; n_equs = eq_list; }, (rfalse, [], [])

let program p =
  let funs = { Hept_mapfold.hept_funs_default with
                 eq = eq; node_dec = node; edesc = edesc } in
  let p, _ = program_it funs (rfalse, [], []) p in
    p

