(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* removing reset statements *)

(* $Id$ *)

open Misc
open Ident
open Heptagon
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

let or_op_call = mk_op ( Ecall(mk_op_desc Initial.por [] Efun, None) )

let pre_true e = {
  e with e_desc = Eapp(mk_op (Epre (Some (Cconstr Initial.ptrue))), [e])
}
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
        or_op res { e with e_desc = Eapp(or_op_call, [mk_bool_var n; e]) }

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
    | Rfalse -> mk_ifthenelse (init e3) e2 e3
    | _ -> (* a reset occurs *)
        mk_ifthenelse (exp_of_res res) e2 e3

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

let add_locals m n locals =
  let rec loop locals i n =
    if i < n then
      loop ((mk_bool_param m.(i)) :: locals) (i+1) n
    else locals in
  loop locals 0 n

let add_local_equations i n m lm acc =
  (* [mi = false;...; m1 = l_m1;...; mn = l_mn] *)
  let rec loop acc k =
    if k < n then
      if k = i
      then loop ((mk_simple_equation (Evarpat (m.(k))) dfalse) :: acc) (k+1)
      else
        loop
          ((mk_simple_equation (Evarpat (m.(k))) (mk_bool_var lm.(k))) :: acc)
          (k+1)
    else acc
  in loop acc 0

let add_global_equations n m lm res acc =
  (* [ l_m1 = if res then true else true fby m1;...;
     l_mn = if res then true else true fby mn ] *)
  let rec loop acc k =
    if k < n then
      let exp =
        (match res with
           | Rfalse -> pre_true (mk_bool_var m.(k))
           | _ -> ifres res dtrue (pre_true (mk_bool_var m.(k)))
        ) in
      loop
        ((mk_equation (Eeq (Evarpat (lm.(k)), exp))) :: acc) (k+1)
    else acc in
  loop acc 0

let defnames m n d =
  let rec loop acc k =
    if k < n
    then loop (Env.add m.(k) (Tid Initial.pbool) acc) (k+1)
    else acc in
  loop d 0

let statefull eq_list = List.exists (fun eq -> eq.eq_statefull) eq_list

let rec translate_eq res v acc_eq_list eq =
  match eq.eq_desc with
    | Ereset(eq_list, e) ->
        let e = translate res e in
        if statefull eq_list then
          let v, acc_eq_list, res = orthen v acc_eq_list res e in
          translate_eqs res v acc_eq_list eq_list
        else
          let _, v, acc_eq_list = equation v acc_eq_list e in
          translate_eqs res v acc_eq_list eq_list
    | Eeq(pat, e) ->
        v, { eq with eq_desc = Eeq(pat, translate res e) } :: acc_eq_list
    | Eswitch(e, tag_block_list) ->
        let e = translate res e in
        let v, tag_block_list, acc_eq_list =
          translate_switch res v acc_eq_list tag_block_list in
        v, { eq with eq_desc = Eswitch(e, tag_block_list) } :: acc_eq_list
    | Epresent _ | Eautomaton _ -> assert false

and translate_eqs res v acc_eq_list eq_list =
  List.fold_left
    (fun (v, acc_eq_list) eq ->
       translate_eq res v acc_eq_list eq) (v, acc_eq_list) eq_list

and translate_switch res locals acc_eq_list switch_handlers =
  (* introduce a reset bit for each branch *)
  let tab_of_vars n = Array.init n (fun _ -> Ident.fresh "r") in
  let n = List.length switch_handlers in
  let m = tab_of_vars n in
  let lm = tab_of_vars n in

  let locals = add_locals m n locals in
  let locals = add_locals lm n locals in

  let body i {w_name = ci;
              w_block = ({ b_local = li; b_defnames = d; b_equs = eqi } as b)} =
    let d = defnames m n d in
    let li, eqi = translate_eqs (rvar (lm.(i))) li [] eqi in
    let eqi = add_local_equations i n m lm eqi in
    { w_name = ci;
      w_block = { b with b_local = li; b_defnames = d; b_equs = eqi } } in

  let rec loop i switch_handlers =
    match switch_handlers with
        [] -> []
      | handler :: switch_handlers ->
          (body i handler) :: (loop (i+1) switch_handlers) in

  let acc_eq_list = add_global_equations n m lm res acc_eq_list in

  locals, loop 0 switch_handlers, acc_eq_list

and translate res e =
  match e.e_desc with
    | Econst _ | Evar _ | Econstvar _ | Elast _ -> e
    | Etuple(e_list) ->
        { e with e_desc = Etuple(List.map (translate res) e_list) }
    | Eapp({a_op = Efby } as op, [e1;e2]) ->
        let e1 = translate res e1 in
        let e2 = translate res e2 in
        begin
          match res, e1 with
            | Rfalse, { e_desc = Econst(c) } ->
                (* no reset *)
                { e with e_desc =
                    Eapp({ op with a_op = Epre(Some c) }, [e2]) }
            | _ ->
                ifres res e1
                  { e with e_desc =
                      Eapp({ op with a_op = Epre(default e1) }, [e2]) }
        end
    | Eapp({ a_op = Earrow }, [e1;e2]) ->
        let e1 = translate res e1 in
        let e2 = translate res e2 in
        ifres res e1 e2

    (* add reset to the current reset exp. *)
    | Eapp({ a_op = Ecall(op_desc, Some re) } as op, e_list) ->
        let re = translate res re in
        let e_list = List.map (translate res) e_list in
        let op = { op with a_op = Ecall(op_desc, Some (or_op res re))} in
        { e with e_desc = Eapp(op, e_list) }
          (* create a new reset exp if necessary *)
    | Eapp({ a_op = Ecall(op_desc, None) } as op, e_list) ->
        let e_list = List.map (translate res) e_list in
        if true_reset res & op_desc.op_kind = Enode then
          let op = { op with a_op = Ecall(op_desc, Some (exp_of_res res)) } in
          { e with e_desc = Eapp(op, e_list) }
        else
          { e with e_desc = Eapp(op, e_list ) }
            (* add reset to the current reset exp. *)
    | Eapp( { a_op = Earray_op (Eiterator(it, op_desc, Some re)) } as op,
            e_list) ->
        let re = translate res re in
        let e_list = List.map (translate res) e_list in
        let r = Some (or_op res re) in
        let op = { op with a_op = Earray_op (Eiterator(it, op_desc, r)) } in
        { e with e_desc = Eapp(op, e_list) }
          (* create a new reset exp if necessary *)
    | Eapp({ a_op = Earray_op (Eiterator(it, op_desc, None)) } as op, e_list) ->
        let e_list = List.map (translate res) e_list in
        if true_reset res then
          let r = Some (exp_of_res res) in
          let op = { op with a_op = Earray_op (Eiterator(it, op_desc, r)) } in
          { e with e_desc = Eapp(op, e_list) }
        else
          { e with e_desc = Eapp(op, e_list) }

    | Eapp(op, e_list) ->
        { e with e_desc = Eapp(op, List.map (translate res) e_list) }
    | Efield(e', field) ->
        { e with e_desc = Efield(translate res e', field) }
    | Estruct(e_f_list) ->
        { e with e_desc =
            Estruct(List.map (fun (f, e) -> (f, translate res e)) e_f_list) }
    | Earray(e_list) ->
        { e with e_desc = Earray(List.map (translate res) e_list) }

let translate_contract ({ c_local = v;
                          c_eq = eq_list;
                          c_assume = e_a;
                          c_enforce = e_g } as c) =
  let v, eq_list = translate_eqs rfalse v [] eq_list in
  let e_a = translate rfalse e_a in
  let e_g = translate rfalse e_g in
  { c with c_local = v; c_eq = eq_list; c_assume = e_a; c_enforce = e_g }

let node (n) =
  let c = optional translate_contract n.n_contract in
  let var, eqs = translate_eqs rfalse n.n_local [] n.n_equs in
  { n with n_local = var; n_equs = eqs; n_contract = c }

let program (p) =
  { p with p_nodes = List.map node p.p_nodes }
