(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* simple initialization analysis. This is almost trivial since   *)
(* input/outputs of a node are forced to be initialized           *)

(* $Id: initialization.ml 615 2009-11-20 17:43:14Z pouzet $ *)

open Misc
open Names
open Idents
open Heptagon
open Types
open Location
open Format

type typ =
  | Iproduct of typ list
  | Ileaf of init

and init =
    { mutable i_desc: init_desc;
      mutable i_index: int }

and init_desc =
  | Izero
  | Ione
  | Ivar
  | Imax of init * init
  | Ilink of init

type kind = | Last of init | Var

type tenv = { i_kind : kind; i_typ : init }

(* typing errors *)
exception Unify

let index = ref 0
let gen_index () = incr index; !index
let new_var () = { i_desc = Ivar; i_index = gen_index () }
let izero = { i_desc = Izero; i_index = gen_index () }
let ione = { i_desc = Ione; i_index = gen_index () }
let imax i1 i2 = { i_desc = Imax(i1, i2); i_index = gen_index () }
let product l = Iproduct(l)
let leaf i = Ileaf(i)

(* basic operation on initialization values *)
let rec irepr i =
  match i.i_desc with
    | Ilink(i_son) ->
        let i_son = irepr i_son in
        i.i_desc <- Ilink(i_son);
        i_son
    | _ -> i

(** Simplification rules for max. Nothing fancy here *)
let max i1 i2 =
  let i1 = irepr i1 in
  let i2 = irepr i2 in
  match i1.i_desc, i2.i_desc with
    | (Izero, Izero) -> izero
    | (Izero, _) -> i2
    | (_, Izero) -> i1
    | (_, Ione) | (Ione, _) -> ione
    | _ -> imax i1 i2

let rec itype = function
  | Iproduct(ty_list) -> itype_list ty_list
  | Ileaf(i) -> i

and itype_list ty_list =
  List.fold_left (fun acc ty -> max acc (itype ty)) izero ty_list

(* saturate an initialization type. Every element must be initialized *)
let rec initialized i =
  let i = irepr i in
  match i.i_desc with
    | Izero -> ()
    | Ivar -> i.i_desc <- Ilink(izero)
    | Imax(i1, i2) -> initialized i1; initialized i2
    | Ilink(i) -> initialized i
    | Ione -> raise Unify

(* build an initialization type from a type *)
let rec skeleton i ty =
  match ty with
    | Tprod(ty_list) -> product (List.map (skeleton i) ty_list)
    | _ -> leaf i

let rec const_skeleton i se =
  match se.se_desc with
    | Stuple l -> product (List.map (const_skeleton i) l)
    | _ -> leaf i

(* sub-typing *)
let rec less left_ty right_ty =
  if left_ty == right_ty then ()
  else
    match left_ty, right_ty with
      | Iproduct(l1), Iproduct(l2) -> List.iter2 less l1 l2
      | Ileaf(i1), Ileaf(i2) -> iless i1 i2
      | _ -> raise Unify

and iless left_i right_i =
  if left_i == right_i then ()
  else
    let left_i = irepr left_i in
    let right_i = irepr right_i in
    if left_i == right_i then ()
    else
      match left_i.i_desc, right_i.i_desc with
        | (Izero, _) | (_, Ione) -> ()
        | _, Izero -> initialized left_i
        | Imax(i1, i2), _ ->
            iless i1 right_i; iless i2 right_i
        | _, Ivar ->
            let left_i = occur_check right_i.i_index left_i in
            right_i.i_desc <- Ilink(left_i)
        | _, Imax(i1, i2) ->
            let i1 = occur_check left_i.i_index i1 in
            let i2 = occur_check left_i.i_index i2 in
            right_i.i_desc <- Ilink(imax left_i (imax i1 i2))
        | _ -> raise Unify

(* an inequation [a < t[a]] becomes [a = t[0]] *)
and occur_check index i =
  match i.i_desc with
    | Izero | Ione -> i
    | Ivar -> if i.i_index = index then izero else i
    | Imax(i1, i2) ->
        max (occur_check index i1) (occur_check index i2)
    | Ilink(i) -> occur_check index i

module Printer = struct
  open Format
  open Pp_tools

  let rec print_init ff i = match i.i_desc with
    | Izero -> fprintf ff "0"
    | Ione -> fprintf ff "1"
    | Ivar -> fprintf ff "0"
    | Imax(i1, i2) -> fprintf ff "@[%a\\/%a@]" print_init i1 print_init i2
    | Ilink(i) -> print_init ff i

  let rec print_type ff = function
    | Ileaf(i) -> print_init ff i
    | Iproduct(ty_list) ->
        fprintf ff "@[%a@]" (print_list_r print_type "("" *"")") ty_list

end

module Error = struct
  open Location

  type error = | Eclash of typ * typ

  exception Error of location * error

  let error loc kind = raise (Error(loc, kind))

  let message loc kind =
    begin match kind with
      | Eclash(left_ty, right_ty) ->
          Format.eprintf "%aInitialization error: this expression has type \
              %a, @\n\
              but is expected to have type %a@."
            print_location loc
            Printer.print_type left_ty
            Printer.print_type right_ty
    end;
    raise Errors.Error
end

let less_exp e actual_ty expected_ty =
  try
    less actual_ty expected_ty
  with | Unify -> Error.message e.e_loc (Error.Eclash(actual_ty, expected_ty))

(** Main typing function *)
let rec typing h e =
  match e.e_desc with
    | Econst c -> const_skeleton izero c
    | Evar(x) | Elast(x) -> let { i_typ = i } = Env.find x h in leaf i
    | Epre(None, e) ->
        initialized_exp h e;
        skeleton ione e.e_ty
    | Epre(Some _, e) ->
        initialized_exp h e;
        skeleton izero e.e_ty
    | Efby (e1, e2) ->
        initialized_exp h e2;
        skeleton (itype (typing h e1)) e.e_ty
    | Eapp({ a_op = Etuple }, e_list, _) ->
        product (List.map (typing h) e_list)
    | Eapp({ a_op = op }, e_list, _) ->
        let i = apply h op e_list in
        skeleton i e.e_ty
    | Estruct(l) ->
        let i =
          List.fold_left
            (fun acc (_, e) -> max acc (itype (typing h e))) izero l in
        skeleton i e.e_ty
    | Eiterator (_, _, _, e_list, _) ->
        List.iter (fun e -> initialized_exp h e) e_list;
        skeleton izero e.e_ty

(** Typing an application *)
and apply h op e_list =
  match op, e_list with
    | Earrow, [e1;e2] ->
        let ty1 = typing h e1 in
        let _ = typing h e2 in
        itype ty1
    | Efield, [e1] ->
        itype (typing h e1)
    | Earray, e_list ->
        List.fold_left
          (fun acc e -> max acc (itype (typing h e))) izero e_list
    | Eifthenelse, [e1; e2; e3] ->
        let i1 = itype (typing h e1) in
        let i2 = itype (typing h e2) in
        let i3 = itype (typing h e3) in
        max i1 (max i2 i3)
    | Etuple, _ -> assert false
    (** TODO: init of safe/unsafe nodes
        This is a tmp fix so that pre x + 1 works.*)
    | (Eequal | Efun { qual = "Pervasives" }), e_list ->
        List.fold_left (fun acc e -> itype (typing h e)) izero e_list
    | _ , e_list ->
        List.iter (fun e -> initialized_exp h e) e_list; izero

and expect h e expected_ty =
  let actual_ty = typing h e in
  less_exp e actual_ty expected_ty

and initialized_exp h e = expect h e (skeleton izero e.e_ty)

let rec typing_pat h = function
  | Evarpat(x) -> let { i_typ = i } = Env.find x h in leaf i
  | Etuplepat(pat_list) ->
      product (List.map (typing_pat h) pat_list)

(** Typing equations *)
let rec typing_eqs h eq_list = List.iter (typing_eq h) eq_list

and typing_eq h eq =
  match eq.eq_desc with
    | Eautomaton(handlers) -> typing_automaton h handlers
    | Eswitch(e, handlers) ->
        initialized_exp h e;
        typing_switch h handlers
    | Epresent(handlers, b) ->
        typing_present h handlers b
    | Ereset(b, e) ->
        initialized_exp h e; ignore (typing_block h b)
    | Eeq(pat, e) ->
        let ty_pat = typing_pat h pat in
        expect h e ty_pat

and typing_switch h handlers =
  let handler { w_block = b } = ignore (typing_block h b) in
  List.iter handler handlers

and typing_present h handlers b =
  let handler { p_cond = e; p_block = b } =
    initialized_exp h e; ignore (typing_block h b) in
  List.iter handler handlers; ignore (typing_block h b)

and typing_automaton h state_handlers =
  (* we make a special treatment for state variables defined in the *)
  (* initial state *)
  let weak { s_unless = sunless } =
    match sunless with | [] -> true | _ -> false in

  (* the set of variables which do have an initial value in the other states *)
  let initialized h { s_block = { b_defnames = l } } =
    Env.fold
      (fun elt _ h ->
         let { i_kind = k; i_typ = i } = Env.find elt h in
         match k with
           | Last _ ->
               let h = Env.remove elt h in
               Env.add elt { i_kind = Last(izero); i_typ = izero } h
           | _ -> h)
      l h in

  (* typing the body of the automaton *)
  let handler h
      { s_state = _; s_block = b; s_until = suntil; s_unless = sunless } =
    let escape h { e_cond = e } =
      initialized_exp h e in

    (* typing the body *)
    let h = typing_block h b in
    List.iter (escape h) suntil;
    List.iter (escape h) sunless in

  match state_handlers with
      (* we do a special treatment for state variables which *)
      (* are defined in the initial state if it cannot be immediately *)
      (* exited *)
    | initial :: other_handlers when weak initial ->
        let h = initialized h initial in
        handler h initial;
        List.iter (handler h) other_handlers
    | _ -> List.iter (handler h) state_handlers

and typing_block h { b_local = dec; b_equs = eq_list } =
  let h_extended = build h dec in
  typing_eqs h_extended eq_list;
  h_extended

(* build an typing environment of initialization types *)
and build h dec =
  let kind = function
    | Heptagon.Var -> { i_kind = Var; i_typ = new_var () }
    | Heptagon.Last(Some _) -> { i_kind = Last(izero); i_typ = izero }
    | Heptagon.Last(None) -> { i_kind = Last(ione); i_typ = new_var () } in
  List.fold_left
    (fun h { v_ident = n; v_last = last } -> Env.add n (kind last) h) h dec

let sbuild h dec =
  List.fold_left
    (fun h { v_ident = n } -> Env.add n { i_kind = Var; i_typ = izero } h) h dec

let typing_contract h contract =
  match contract with
    | None -> h
    | Some { c_block = b; c_assume = e_a;
             c_enforce = e_g } ->
        let h' = build h b.b_local in
        typing_eqs h' b.b_equs;
        (* assumption *)
        expect h' e_a (skeleton izero e_a.e_ty);
        (* property *)
        expect h' e_g (skeleton izero e_g.e_ty);
        h

let typing_node { n_name = f; n_input = i_list; n_output = o_list;
                  n_contract = contract; n_block = b } =
  let h = sbuild Env.empty i_list in
  let h = sbuild h o_list in
  let h = typing_contract h contract in
    ignore (typing_block h b)

let program ({ p_nodes = p_node_list } as p) =
  List.iter typing_node p_node_list;
  p


