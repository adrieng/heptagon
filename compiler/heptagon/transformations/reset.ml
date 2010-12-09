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
open Idents
open Heptagon
open Hept_mapfold
open Types
open Initial

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
   every res

   ---->

   switch e with
     case C1 do ... (* l_m1 *)
                m1 = false; m2 = l_m2; m3 = l_m3
   | case C2 do ... (* l_m2 *)
                m1 = l_m1; m2 = false; m3 = l_m3
   | case C3 do ... (* l_m3 *)
                m1 = l_m1; m2 = l_m2; m3 = false
   end;
   l_m1 = if res then true else (true fby m1);
   l_m2 = if res then true else (true fby m2);
   l_m3 = if res then true else (true fby m3);

   e1 -> e2 is translated into if (true fby false) then e1 else e2
*)

let mk_bool_var n = mk_exp (Evar n) (Tid Initial.pbool)
let mk_bool_param n = mk_var_dec n (Tid Initial.pbool)

let or_op_call e_list = mk_op_app (Efun Initial.por) e_list

let pre_true e =
  { e with e_desc = Epre (Some (mk_static_bool true), e) }
let init e = pre_true { dfalse with e_loc = e.e_loc }

let add_resets res e =
  match res, e with
    | None, _ -> e
    | _, None -> res
    | Some re, Some e -> Some { e with e_desc = or_op_call [re; e] }

let default e =
  match e.e_desc with
    | Econst c -> Some c
    | _ -> None

let ifres res e2 e3 =
  match res with
    | None -> mk_op_app Eifthenelse [init e3; e2; e3]
    | Some re -> (* a reset occurs *)
        mk_op_app Eifthenelse [re; e2; e3]

(* add an equation *)
let equation v acc_eq_list e =
  let n = Idents.fresh "r" in
  n,
  (mk_bool_param n) :: v,
  (mk_equation (Eeq(Evarpat n, e))) ::acc_eq_list

let orthen v acc_eq_list res e =
  match e.e_desc with
    | Evar _ -> add_resets res (Some e), v, acc_eq_list
    | _ ->
        let n, v, acc_eq_list = equation v acc_eq_list e in
          add_resets res (Some { e with e_desc = Evar n }), v, acc_eq_list

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
       | None -> pre_true (mk_bool_var m)
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
           | None, { e_desc = Econst c } ->
               (* no reset *)
               Epre(Some c, e2)
           | _ ->
               ifres res e1
                 { e2 with e_desc = Epre(default e1, e2) }
        )
    | Eapp({ a_op = Earrow }, [e1;e2], _) ->
        ifres res e1 e2

    (* add reset to the current reset exp. *)
    | Eapp({ a_op = Enode _ } as op, e_list, re) ->
        Eapp(op, e_list, add_resets res re)
    (* add reset to the current reset exp. *)
    | Eiterator(it, ({ a_op = Enode _ } as op), n, e_list, re) ->
        Eiterator(it, op, n, e_list, add_resets res re)
    | _ -> ed
  in
    ed, (res, v, acc_eq_list)

let switch_handlers funs (res, v, acc_eq_list) switch_handlers =
  (* introduce a reset bit for each branch *)
  let m_list = List.map (fun _ -> Idents.fresh "r") switch_handlers in
  let lm_list = List.map (fun _ -> Idents.fresh "r") switch_handlers in

  let body i ({ w_block = b } as sh) m lm =
    let defnames = List.fold_left (fun acc m ->
           Env.add m (Tid Initial.pbool) acc) b.b_defnames m_list in
    let _, (_, v, acc_eq_list) =
      mapfold (eq_it funs) (Some (mk_bool_var lm), b.b_local, []) b.b_equs in
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

    | Ereset(b, e) -> (* LG TODO deal with real blocks, transform into a block*)
        let e, _ = exp_it funs (res, v, acc_eq_list) e in
        let res, v, acc_eq_list =
         (* if statefull eq_list then*)
            orthen v acc_eq_list res e
         (* else
            let _, v, acc_eq_list = equation v acc_eq_list e in
              res, v, acc_eq_list*)
        in
        let _, (res, v, acc_eq_list) =
          mapfold (eq_it funs) (res, v, acc_eq_list) b.b_equs in
          equ, (res, v, acc_eq_list)

    | _ ->
        let equ, (res, v, acc_eq_list) = eq funs (res, v, acc_eq_list) equ in
          equ, (res, v, equ::acc_eq_list)

(** throw away the old block and
    reconstruct it from the accumulated eq_list
    and add to the locals the new vars.
    The acc_eq_list should contain all wanted equations, even old ones. *)
let block funs acc b =
  let _, (_, v, eq_list) = Hept_mapfold.block funs (None, [], []) b in
    { b with b_local = v @ b.b_local; b_equs = eq_list; }, acc

let program p =
  let funs = { Hept_mapfold.defaults with
                 eq = eq; block = block; edesc = edesc } in
  let p, _ = program_it funs (None, [], []) p in
    p
