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
(* add a special treatment of clock state variables whose initial *)
(* values are known. This allows to accept code generated         *)
(* for automata *)
(* if [clock c = C fby ec] then [merge c (C -> e) ...] is initialized *)
(* if [e] is initialized only *)

(* $Id: init.ml 615 2009-11-20 17:43:14Z pouzet $ *)

open Misc
open Names
open Ident
open Minils
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

type typ_env =
    { t_init: init; (* its initialisation type *)
      t_value: longname option; (* its initial value *)
    }

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
    | Tbase _ -> leaf i
    | Tprod(ty_list) -> product (List.map (skeleton i) ty_list)

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

(* computes the initialization type of a merge *)
let merge opt_c c_i_list =
  let rec search c c_i_list =
    match c_i_list with
      | [] -> izero
      | (c0, i) :: c_i_list -> if c = c0 then i else search c c_i_list in
  match opt_c with
    | None -> List.fold_left (fun acc (_, i) -> max acc i) izero c_i_list
    | Some(c) -> search c c_i_list
 
module Printer = struct
  open Format

  let rec print_list_r print po sep pf ff = function
  | [] -> ()
  | x :: l ->
      fprintf ff "@[%s%a" po print x;
      List.iter (fprintf ff "%s@]@ @[%a" sep print) l;
      fprintf ff "%s@]" pf

  let rec fprint_init ff i = match i.i_desc with
    | Izero -> fprintf ff "0"
    | Ione -> fprintf ff "1"
    | Ivar -> fprintf ff "0"
    | Imax(i1, i2) -> fprintf ff "@[%a\\/%a@]" fprint_init i1 fprint_init i2
    | Ilink(i) -> fprint_init ff i

  let rec fprint_typ ff = function
    | Ileaf(i) -> fprint_init ff i
    | Iproduct(ty_list) ->
        fprintf ff "@[%a@]" (print_list_r fprint_typ "("" *"")") ty_list

  let output_typ oc ty =
    let ff = formatter_of_out_channel oc in
    fprintf ff "@[";
    fprint_typ ff ty;
    fprintf ff "@?@]"
end

module Error = struct
  open Location

  type error = | Eclash of typ * typ

  exception Error of location * error

  let error loc kind = raise (Error(loc, kind))

  let message loc kind =
    begin match kind with
        | Eclash(left_ty, right_ty) ->
            Printf.eprintf "%aInitialization error: this expression has type \
              %a, \n\
              but is expected to have type %a\n"
              output_location loc
              Printer.output_typ left_ty
              Printer.output_typ right_ty
    end;
    raise Misc.Error
end

let less_exp e actual_ty expected_ty =
  try
    less actual_ty expected_ty
  with | Unify -> Error.message e.e_loc (Error.Eclash(actual_ty, expected_ty))
  
let rec typing h e =
  match e.e_desc with
    | Econst(c) -> leaf izero
    | Evar(x) -> let { t_init = i } = Env.find x h in leaf i
    | Efby(None, e) -> 
	expect h e (skeleton izero e.e_ty); 
	leaf ione
    | Efby(Some _, e) -> 
	expect h e (skeleton izero e.e_ty); 
	leaf izero
    | Etuple(e_list) ->
	product (List.map (typing h) e_list)
    | Eop(_, e_list) ->
	let i = List.fold_left (fun acc e -> itype (typing h e)) izero e_list in
	skeleton i e.e_ty
    | Eapp(_, e_list) ->
	List.iter (fun e -> expect h e (skeleton izero e.e_ty)) e_list;
	skeleton izero e.e_ty
    | Eevery(_, e_list, n) ->
	List.iter (fun e -> expect h e (skeleton izero e.e_ty)) e_list;
	let { t_init = i } = Env.find n h in
	skeleton i e.e_ty
    | Ewhen(e, c, n) ->
	let { t_init = i1 } = Env.find n h in
	let i2 = itype (typing h e) in
	skeleton (max i1 i2) e.e_ty
    | Eifthenelse(e1, e2, e3) ->
	let i1 = itype (typing h e1) in
	let i2 = itype (typing h e2) in
	let i3 = itype (typing h e3) in
	let i = max i1 (max i2 i3) in
	skeleton i e.e_ty
    | Emerge(n, c_e_list) ->
	let { t_init = i; t_value = opt_c } = Env.find n h in
        let i =
	  merge opt_c 
	    (List.map (fun (c, e) -> (c, itype (typing h e))) c_e_list)	in
	skeleton i e.e_ty
    | Efield(e1,n) ->
	let i = itype (typing h e1) in
	skeleton i e.e_ty
    | Estruct(l) ->
	let i =
	  List.fold_left
	    (fun acc (_, e) -> max acc (itype (typing h e))) izero l in
	skeleton i e.e_ty

and expect h e expected_ty =
  let actual_ty = typing h e in
  less_exp e actual_ty expected_ty

let rec typing_pat h = function
  | Evarpat(x) -> let { t_init = i } = Env.find x h in leaf i
  | Etuplepat(pat_list) ->
      product (List.map (typing_pat h) pat_list)

let typing_eqs h eq_list =
  List.iter 
    (fun { p_lhs = pat; p_rhs = e } ->
      let ty_pat = typing_pat h pat in
      expect h e ty_pat) eq_list

let build h eq_list =
  let rec build_pat h = function
    | Evarpat(x) -> Env.add x { t_init = new_var (); t_value = None } h
    | Etuplepat(pat_list) -> List.fold_left build_pat h pat_list in
  let build_equation h { p_lhs = pat; p_rhs = e } =
    match pat, e.e_desc with
      | Evarpat(x), Efby(Some(Cconstr c), _) -> 
	  (* we keep the initial value of state variables *)
	  Env.add x { t_init = new_var (); t_value = Some(c) } h 
      | _ -> build_pat h pat in
 List.fold_left build_equation h eq_list

let sbuild h dec =
  List.fold_left 
    (fun h { v_name = n } -> Env.add n { t_init = izero; t_value = None } h)
    h dec    

let typing_contract h contract =
  match contract with
    | None -> h
    | Some { c_local = l_list; c_eq = eq_list; c_assume = e_a; 
	     c_enforce = e_g; c_controllables = c_list } ->
	let h = sbuild h c_list in
	let h' = build h eq_list in
	typing_eqs h' eq_list;
	(* assumption *)
	expect h' e_a (skeleton izero e_a.e_ty);
	(* property *)
	expect h' e_g (skeleton izero e_g.e_ty);
	h

let typing_node { n_name = f; n_input = i_list; n_output = o_list;
		  n_contract = contract;
		  n_local = l_list; n_equs = eq_list } =
  let h = sbuild Env.empty i_list in
  let h = sbuild h o_list in
  let h = typing_contract h contract in

  let h = build h eq_list in
  typing_eqs h eq_list

let program ({ p_nodes = p_node_list } as p) =
  List.iter typing_node p_node_list;
  p


