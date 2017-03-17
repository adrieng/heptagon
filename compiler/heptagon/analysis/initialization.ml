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

(** {2 Simple initialization analysis}
  The initialization analysis only deals with the first instant of flows.
  Things are easy since input/outputs of a node are considered initialized.
  It is allowed to have uninitialized inputs for safe nodes,
   it will consider the result as uninitialized.
  [last x] is initialized when either it was declared with an initial value
   or when [x] is defined in the initial state of an automaton. *)


(* Requis : typage *)

open Misc
open Idents
open Heptagon
open Types
open Location

type typ =
  | Iproduct of typ list
  | Ileaf of init

and init = initr ref
and initr =
  | Izero
  | Ione of root
  | Ivar of int
  | Imax of init * init
  | Ilink of init

(* try to keep track of the root of the uninitialized state *)
and root =
  | RLast_none of ident
  | RExp of exp
  | ROr of root * root

(* typing errors *)
exception Unify of root

(** unalias [init] type *)
let rec irepr i =
  match !i with
    | Ilink(i_son) ->
        let i_son = irepr i_son in
        i := Ilink(i_son); (* shorten path *)
        i_son
    | _ -> i

let _index = ref 0
let new_var () =
  let gen_index () = incr _index; !_index in
  ref (Ivar(gen_index ()))

let izero = ref Izero
let ione root = ref (Ione root)

(** max between types with some basic simplifications *)
let imax i1 i2 =
  let i1 = irepr i1 in
  let i2 = irepr i2 in
  match !i1, !i2 with
    | (Izero, Izero) -> izero
    | (Izero, _) -> i2
    | (_, Izero) -> i1
    | (Ione r1, Ione r2) -> ione (ROr(r1, r2))
    | (_, Ione r) | (Ione r, _) -> ione r
    | _ -> ref (Imax(i1, i2))

let product l = Iproduct(l)
let leaf i = Ileaf(i)

(** Typing Environment *)
module IEnv =
struct
  type k = | Last of ident | Var of ident
  type v = init
  include (Map.Make (struct type t = k let compare = compare end))

  let find_var x h = find (Var x) h
  let find_last x h = find (Last x) h

  let find_var_typ x h = leaf (find_var x h)
  let find_last_typ x h = leaf (find_last x h)

  let add_var x v h = add (Var x) v h
  let add_last x v h = add (Last x) v h

  let _add_var_dec def h vd =
    let h = add_var vd.v_ident def h in
    match vd.v_last with
      | Heptagon.Var -> h
      | Heptagon.Last None ->
          add_last vd.v_ident (ione (RLast_none vd.v_ident)) h (* last is not initialized *)
      | Heptagon.Last (Some _) ->
          add_last vd.v_ident izero h (* last is initialized *)

  let add_initd_var_dec h vd = _add_var_dec izero h vd
  let add_var_dec h vd = _add_var_dec (new_var ()) h vd
end

(** return the representative of a [typ] ( the max ) *)
let rec itype = function
  | Iproduct(ty_list) ->
      List.fold_left (fun acc ty -> imax acc (itype ty)) izero ty_list
  | Ileaf(i) -> i

(** saturate an [init] type. Every element must be initialized *)
let rec force_initialized i =
  let i = irepr i in
  match !i with
    | Izero -> ()
    | Ivar _ -> i := Ilink(izero)
    | Imax(i1, i2) -> force_initialized i1; force_initialized i2
    | Ilink(i) -> force_initialized i
    | Ione r -> raise (Unify r)

(** build a [typ] from a [ty] *)
let rec skeleton i ty =
  match ty with
    | Tprod(ty_list) -> product (List.map (skeleton i) ty_list)
    | _ -> leaf i

(** sub-typing *)
let rec less left_ty right_ty =
  (* an inequation [a < t[a]] becomes [a = t[0]] *)
  let rec occur_check index i =
    match !i with
      | Izero | Ione _ -> i
      | Ivar id -> if id = index then izero else i
      | Imax(i1, i2) -> imax (occur_check index i1) (occur_check index i2)
      | Ilink(i) -> occur_check index i
  in
  (* sub-typing on [init] *)
  let rec iless left_i right_i =
    let left_i = irepr left_i in
    let right_i = irepr right_i in
    if left_i == right_i then ()
    else match !left_i, !right_i with
      | Izero, _ -> ()
      | _, Ione _ -> ()
      | _, Izero -> force_initialized left_i
      | Imax(i1, i2), _ -> iless i1 right_i; iless i2 right_i
      | _, Ivar id ->
          let left_i = occur_check id left_i in
          right_i := Ilink left_i
      | Ivar id, Imax(i1, i2) ->
          let i1 = occur_check id i1 in
          let i2 = occur_check id i2 in
          right_i := Ilink(imax left_i (imax i1 i2))
      | Ione r, Imax _ -> raise (Unify r)
      | Ilink _, _ | _, Ilink _ -> assert false
  in
  if left_ty == right_ty then ()
  else match left_ty, right_ty with
    | Iproduct(l1), Iproduct(l2) -> List.iter2 less l1 l2
    | Ileaf(i1), Ileaf(i2) -> iless i1 i2
    | _ -> assert false


module Printer = struct
  open Format
  open Pp_tools

  let rec print_init ff i = match !i with
    | Izero -> fprintf ff "initialized"
    | Ione _ -> fprintf ff "not initialized"
    | Ivar(i) -> fprintf ff "ivar_%i" i
    | Imax(i1, i2) -> fprintf ff "@[<4>max %a@ %a@]" print_init i1 print_init i2
    | Ilink(i) -> print_init ff i

  let rec print_type ff = function
    | Ileaf(i) -> print_init ff i
    | Iproduct(ty_list) ->
        fprintf ff "@[%a@]" (print_list_r print_type "("" *"")") ty_list

  let rec print_root ff = function
    | RLast_none(i) ->
        fprintf ff "that last %a should be initialized" print_ident i
    | RExp(e) ->
        fprintf ff "the expression :@\n  @[%a@]" print_location e.e_loc
    | ROr(r1,r2) ->
        fprintf ff "@\n- %a@\n- or %a" print_root r1 print_root r2
end

module Error = struct
  type error = | Eclash of root * typ * typ

  exception Error of location * error

  let error loc kind = raise (Error(loc, kind))

  let message loc kind =
    begin match kind with
      | Eclash(root, left_ty, right_ty) ->
          Format.eprintf
            "Initialization error :@\n%a\
             this expression is %a,@ but is expected to be %a,\
             @ the root of the conflict is %a.@."
            print_location loc
            Printer.print_type left_ty
            Printer.print_type right_ty
            Printer.print_root root
    end;
    raise Errors.Error
end

let less_exp e actual_ty expected_ty =
  try
    less actual_ty expected_ty
  with Unify r -> Error.message e.e_loc (Error.Eclash(r,actual_ty, expected_ty))

(** Main typing function *)
let rec typing h e =
  match e.e_desc with
    | Econst _ -> skeleton izero e.e_ty
    | Evar(x) -> IEnv.find_var_typ x h
    | Elast(x) -> IEnv.find_last_typ x h
    | Epre(None, e1) ->
        initialized_exp h e1;
        skeleton (ione (RExp e)) e1.e_ty
    | Epre(Some _, e) ->
        initialized_exp h e;
        skeleton izero e.e_ty
    | Efby (e1, e2) ->
        initialized_exp h e2;
        skeleton (itype (typing h e1)) e.e_ty
    | Eapp({ a_op = Etuple }, e_list, _) ->
        product (List.map (typing h) e_list)
    | Eapp(app, e_list, _) ->
        let i = apply h app e_list in
        skeleton i e.e_ty
    | Estruct(l) ->
        let i =
          List.fold_left
            (fun acc (_, e) -> imax acc (itype (typing h e))) izero l in
        skeleton i e.e_ty
    | Eiterator (_, _, _, pe_list, e_list, _) ->
        List.iter (fun e -> initialized_exp h e) pe_list;
        List.iter (fun e -> initialized_exp h e) e_list;
        skeleton izero e.e_ty
    | Ewhen (e, _, x) ->
        let i = imax (IEnv.find_var x h) (itype (typing h e)) in
        skeleton i e.e_ty
    | Emerge (x, c_e_list) ->
        let i =
          List.fold_left
            (fun acc (_, e) -> imax acc (itype (typing h e))) izero c_e_list in
        let i = imax (IEnv.find_var x h) i in
        skeleton i e.e_ty
    | Esplit (c, e2) ->
        let i = imax (itype (typing h c)) (itype (typing h e2)) in
          skeleton i e.e_ty

(** Typing an application *)
and apply h app e_list =
  match app.a_op with
    | Earrow ->
        let e1,e2 = assert_2 e_list in
        let ty1 = typing h e1 in
        let _ = typing h e2 in
        itype ty1
    | Enode _ ->
       begin
         (* for nodes, force all inputs to be initialized *)
         List.iter (fun e -> initialized_exp h e) e_list;
         izero
       end
    | _ ->
       List.fold_left (fun acc e -> imax acc (itype (typing h e))) izero e_list


and expect h e expected_ty =
  let actual_ty = typing h e in
  less_exp e actual_ty expected_ty

and initialized_exp h e = expect h e (skeleton izero e.e_ty)

let rec typing_pat h = function
  | Evarpat(x) -> IEnv.find_var_typ x h
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
    | Eblock b ->
        ignore (typing_block h b)
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

  (* Set in the env [last x] as initialized if [x] is initialized here *)
  let initialized h { s_block = { b_defnames = l } } =
    let env_update x h =
      try
        let _xl = IEnv.find_last x h in (* it's a last in the env, good. *)
        IEnv.add_last x (IEnv.find_var x h) h
      with Not_found -> h (* nothing to do *)
    in
    Env.fold (fun x _ h -> env_update x h) l h in

  let handler h { s_state = _; s_block = b; s_until = suntil; s_unless = sunless } =
    let escape h { e_cond = e } = initialized_exp h e in
    (* typing the body *)
    let h = typing_block h b in
    List.iter (escape h) suntil;
    List.iter (escape h) sunless
  in

  (* typing the body of the automaton *)
  match state_handlers with
      (* we do a special treatment for state variables which *)
      (* are defined in the initial state if it cannot be immediately exited *)
    | initial :: other_handlers when weak initial ->
        handler h initial; (* first type it *)
        let h = initialized h initial in
        (* then type the others in the env of the first one *)
        List.iter (handler h) other_handlers
    | _ -> List.iter (handler h) state_handlers

and typing_block h { b_local = dec; b_equs = eq_list } =
  let h_extended = build h dec in
  typing_eqs h_extended eq_list;
  h_extended

(* add var_decs to a typing environment *)
and build h vdecs =
  List.fold_left IEnv.add_var_dec h vdecs

(* add var_decs as initialized to a typing environement *)
let build_initialized h vdecs =
  List.fold_left IEnv.add_initd_var_dec h vdecs

let typing_contract h contract =
  match contract with
    | None -> h
    | Some { c_block = b;
             c_assume = e_a;
             c_objectives = objs;
             c_controllables = c } ->
        let h' = build h b.b_local in
        typing_eqs h' b.b_equs;
        (* assumption *)
        expect h' e_a (skeleton izero e_a.e_ty);
        (* property *)
        List.iter (fun o -> expect h' o.o_exp (skeleton izero o.o_exp.e_ty)) objs;
        build_initialized h c

let typing_node { n_input = i_list; n_output = o_list;
                  n_contract = contract; n_block = b } =
  let h = build_initialized IEnv.empty i_list in
  let h = build_initialized h o_list in
  let h = typing_contract h contract in
    ignore (typing_block h b)

let program ({ p_desc = pd } as p) =
  List.iter (function Pnode n -> typing_node n | _ -> ()) pd;
  p
