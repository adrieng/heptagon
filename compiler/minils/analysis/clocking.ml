(**************************************************************************)
(*                                                                        *)
(*  MiniLustre                                                            *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* clock checking *)

open Misc
open Idents
open Minils
open Mls_printer
open Signature
open Types
open Clocks
open Location
open Format

(** Error Kind *)
type error_kind = | Etypeclash of ct * ct

let error_message loc = function
  | Etypeclash (actual_ct, expected_ct) ->
      Format.eprintf "%aClock Clash: this expression has clock %a,@\n\
                        but is expected to have clock %a.@."
        print_location loc
        print_clock actual_ct
        print_clock expected_ct;
      raise Errors.Error


let typ_of_name h x = Env.find x h

let rec typing h e =
  let ct = match e.e_desc with
    | Econst se -> skeleton (fresh_clock ()) se.se_ty
    | Evar x -> Ck (typ_of_name h x)
    | Efby (_, e) -> typing h e
    | Eapp({a_op = op}, args, r) ->
        let ck = match r with
          | None -> fresh_clock ()
          | Some(reset) -> typ_of_name h reset in
        typing_op op args h e ck
    | Eiterator (_, _, _, args, r) -> (* Typed exactly as a fun or a node... *)
        let ck = match r with
          | None -> fresh_clock()
          | Some(reset) -> typ_of_name h reset
        in (List.iter (expect h (Ck ck)) args; skeleton ck e.e_ty)
    | Ewhen (e, c, n) ->
        let ck_n = typ_of_name h n in
        (expect h (skeleton ck_n e.e_ty) e; skeleton (Con (ck_n, c, n)) e.e_ty)
    | Emerge (n, c_e_list) ->
        let ck_c = typ_of_name h n in
        (typing_c_e_list h ck_c n c_e_list; skeleton ck_c e.e_ty)
    | Estruct l ->
        let ck = fresh_clock () in
        (List.iter
           (fun (_, e) -> let ct = skeleton ck e.e_ty in expect h ct e) l;
         Ck ck)
  in (e.e_ck <- ckofct ct; ct)

and typing_op op e_list h e ck = match op with
  | (Eequal | Efun _ | Enode _) -> (*LA*)
      List.iter (fun e -> expect h (skeleton ck e.e_ty) e) e_list;
      skeleton ck e.e_ty
  | Etuple ->
      Cprod (List.map (typing h) e_list)
  | Eifthenelse ->
      let e1, e2, e3 = assert_3 e_list in
      let ct = skeleton ck e.e_ty
      in (expect h (Ck ck) e1; expect h ct e2; expect h ct e3; ct)
  | Efield ->
      let e1 = assert_1 e_list in
      let ct = skeleton ck e1.e_ty in (expect h (Ck ck) e1; ct)
  | Efield_update ->
      let e1, e2 = assert_2 e_list in
      let ct = skeleton ck e.e_ty
      in (expect h (Ck ck) e1; expect h ct e2; ct)
  | Earray ->
      (List.iter (expect h (Ck ck)) e_list; skeleton ck e.e_ty)
  | Earray_fill -> let e = assert_1 e_list in typing h e
  | Eselect -> let e = assert_1 e_list in typing h e
  | Eselect_dyn -> (* TODO defe not treated ? *)
      let e1, defe, idx = assert_2min e_list in
      let ct = skeleton ck e1.e_ty
      in (List.iter (expect h ct) (e1::defe::idx); ct)
  | Eupdate ->
      let e1, e2, idx = assert_2min e_list in
      let ct = skeleton ck e.e_ty
      in (expect h (Ck ck) e1; expect h ct e2; List.iter (expect h ct) idx; ct)
  | Eselect_slice -> let e = assert_1 e_list in typing h e
  | Econcat ->
      let e1, e2 = assert_2 e_list in
      let ct = skeleton ck e.e_ty
      in (expect h (Ck ck) e1; expect h ct e2; ct)

and expect h expected_ty e =
  let actual_ty = typing h e in
  try unify actual_ty expected_ty
  with
  | Unify -> eprintf "%a : " print_exp e;
      error_message e.e_loc (Etypeclash (actual_ty, expected_ty))

and typing_c_e_list h ck_c n c_e_list =
  let rec typrec =
    function
      | [] -> ()
      | (c, e) :: c_e_list ->
          (expect h (skeleton (Con (ck_c, c, n)) e.e_ty) e; typrec c_e_list)
  in typrec c_e_list

let rec typing_pat h =
  function
    | Evarpat x -> Ck (typ_of_name h x)
    | Etuplepat pat_list -> Cprod (List.map (typing_pat h) pat_list)

let typing_eqs h eq_list = (*TODO FIXME*)
  let typing_eq { eq_lhs = pat; eq_rhs = e } =
    let ty_pat = typing_pat h pat in
    (try expect h ty_pat e with
      | Errors.Error -> (* DEBUG *)
          Format.eprintf "Complete expression: %a@\nClock pattern: %a@."
            Mls_printer.print_exp e
            Mls_printer.print_clock ty_pat;
          raise Errors.Error)
  in List.iter typing_eq eq_list

let build h dec =
  List.fold_left (fun h { v_ident = n } -> Env.add n (fresh_clock ()) h) h dec

let sbuild h dec base =
  List.fold_left (fun h { v_ident = n } -> Env.add n base h) h dec

let typing_contract h contract base =
  match contract with
    | None -> h
    | Some { c_local = l_list;
             c_eq = eq_list;
             c_assume = e_a;
             c_enforce = e_g;
						 c_controllables = c_list } ->
        let h' = build h l_list in
        (* assumption *)
        (* property *)
        typing_eqs h' eq_list;
        expect h' (Ck base) e_a;
        expect h' (Ck base) e_g;
        sbuild h c_list base

let typing_node ({ n_input = i_list;
                   n_output = o_list;
                   n_contract = contract;
                   n_local = l_list;
                   n_equs = eq_list
                 } as node) =
  let base = Cbase in
  let h = sbuild Env.empty i_list base in
  let h = sbuild h o_list base in
  let h = typing_contract h contract base in
  let h = build h l_list in
  (typing_eqs h eq_list;
   (*update clock info in variables descriptions *)
   let set_clock vd = { vd with v_clock = ck_repr (Env.find vd.v_ident h) } in
   { (node) with
       n_input = List.map set_clock i_list;
       n_output = List.map set_clock o_list;
       n_local = List.map set_clock l_list })

let program (({ p_nodes = p_node_list } as p)) =
  { (p) with p_nodes = List.map typing_node p_node_list; }

