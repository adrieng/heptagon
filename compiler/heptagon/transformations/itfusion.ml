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
open Signature
open Modules
open Names
open Static
open Hept_mapfold
open Heptagon
open Hept_utils
(* Iterator fusion *)

let is_stateful app =
  match app.a_op with
    | Enode _ -> true
    | _ -> false

(* Functions to temporarily store anonymous nodes*)
let mk_fresh_node_name () = Modules.fresh_value "itfusion" "temp"

let fresh_vd_of_arg a =
  Idents.gen_fresh "itfusion"
                   (fun a -> match a.a_name with
                             | None -> "v"
                             | Some n -> n) a

let fresh_var () = Idents.gen_var "itfusion" "x"

let anon_nodes = ref QualEnv.empty

let add_anon_node inputs outputs locals eqs =
  let n = mk_fresh_node_name () in
  let b = mk_block ~locals:locals eqs in
  let nd = Hept_utils.mk_node ~input:inputs ~output:outputs n b in
  anon_nodes := QualEnv.add n nd !anon_nodes;
  n

let replace_anon_node n nd =
  anon_nodes := QualEnv.add n nd !anon_nodes

let find_anon_node n =
  QualEnv.find n !anon_nodes

let is_anon_node n =
  QualEnv.mem n !anon_nodes

let are_equal n m =
  let n = simplify QualEnv.empty n in
  let m = simplify QualEnv.empty m in
    n = m

let pat_of_vd_list l =
match l with
  | [vd] -> Evarpat (vd.v_ident)
  | _ -> Etuplepat (List.map (fun vd -> Evarpat vd.v_ident) l)

let type_of_vd_list l =
  Types.prod (List.map (fun vd -> vd.v_type) l)

let linearity_of_vd_list l =
  Linearity.prod (List.map (fun vd -> vd.v_linearity) l)

let exp_of_vd vd =
  mk_exp (Evar vd.v_ident) vd.v_type ~linearity:vd.v_linearity

let tuple_of_vd_list l =
  let el = List.map exp_of_vd l in
  let ty = type_of_vd_list l in
  let lin = linearity_of_vd_list l in
    mk_exp (Eapp (mk_app Etuple, el, None)) ty ~linearity:lin

let vd_of_arg ad =
    mk_var_dec (fresh_vd_of_arg ad) ad.a_type ~linearity:ad.a_linearity

(** @return the lists of inputs and outputs (as var_dec) of
    an app object. *)
let get_node_inp_outp app = match app.a_op with
  | (Enode f | Efun f) when is_anon_node f ->
    (* first check if it is an anonymous node *)
    let nd = find_anon_node f in
      nd.n_input, nd.n_output
  | Enode f | Efun f ->
      (* it is a regular node*)
    let ty_desc = find_value f in
    let new_inp = List.map vd_of_arg ty_desc.node_outputs in
    let new_outp = List.map vd_of_arg ty_desc.node_outputs in
      new_inp, new_outp
  | _ -> assert false

(** Creates the equation to call the node [app].
    @return the list of new inputs required by the call, the expression
    used to retrieve the result of the call and [acc_eq_list] with the
    added equations. *)
let mk_call app acc_eq_list =
  let new_inp, new_outp = get_node_inp_outp app in
  let args = List.map exp_of_vd new_inp in
  let out_ty = type_of_vd_list new_outp in
  let out_lin = linearity_of_vd_list new_outp in
  let e = mk_exp (Eapp (app, args, None)) out_ty ~linearity:out_lin in
  match List.length new_outp with
    | 1 -> new_inp, e, acc_eq_list
    | _ ->
        (*more than one output, we need to create a new equation *)
        let eq = mk_equation (Eeq(pat_of_vd_list new_outp, e)) in
        let e = tuple_of_vd_list new_outp in
          new_inp, e, eq::acc_eq_list

let edesc funs acc ed =
  let ed, acc = Hept_mapfold.edesc funs acc ed in
  match ed with
    | Eiterator(Imap, f, n, [], e_list, r) ->
        (* @return the list of inputs of the anonymous function,
            a list of created equations (the body of the function),
            the args for the call of f in the lambda,
            the args for the iterator (ie the arrays).
            [b] is used to know whether some fusion can be done.

            map f (map g (x, y), z) --->
                   fun x', y', z' -> o1, o2 with
                        _v1, _v2 = g(x',y')
                        o1, o2 = f (_v1, _v2, z')
        *)
        let mk_arg e (inp, acc_eq_list, largs, args, b) = match e.e_desc with
          | Eiterator(Imap, g, m, [], local_args, _) when List.for_all2 are_equal n m ->
              let new_inp, e, acc_eq_list = mk_call g acc_eq_list in
              new_inp @ inp, acc_eq_list, e::largs, local_args @ args, true
          | _ ->
              let vd = mk_var_dec (fresh_var ()) e.e_ty ~linearity:e.e_linearity in
              vd::inp, acc_eq_list, (exp_of_vd vd)::largs, e::args, b
        in

        let inp, acc_eq_list, largs, args, can_be_fused =
          List.fold_right mk_arg e_list ([], [], [], [], false) in
        if can_be_fused
        then (
          (* create the call to f in the lambda fun *)
          let _, outp = get_node_inp_outp f in
          let f_out_type = type_of_vd_list outp in
          let f_out_lin = linearity_of_vd_list outp in
          let call = mk_exp (Eapp(f, largs, None)) f_out_type ~linearity:f_out_lin in
          let eq = mk_equation (Eeq(pat_of_vd_list outp, call)) in
          (* create the lambda *)
          let anon = mk_app
            (Enode (add_anon_node inp outp [] (eq::acc_eq_list))) in
          Eiterator(Imap, anon, n, [], args, r), acc)
        else
          ed, acc


    | _ -> raise Errors.Fallback


let program p =
  let funs = { Hept_mapfold.defaults with edesc = edesc } in
  let p, _ = Hept_mapfold.program_it funs false p in
  let pd =
    QualEnv.fold
      (fun _ nd l ->
         Modules.add_value nd.n_name (signature_of_node nd);
         Pnode nd :: l)
      !anon_nodes
      p.p_desc in
    { p with p_desc = pd }
