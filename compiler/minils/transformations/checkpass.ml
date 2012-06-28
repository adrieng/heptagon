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

open Misc
open Names
open Idents
open Signature
open Minils
open Mls_utils
open Mls_printer
open Global_printer
open Types
open Clocks

let add_check prefix pass nd nd_list =
  if nd.n_input <> []
  then (Format.eprintf "Cannot generate check for node %a with inputs"
          print_qualname nd.n_name; assert false)
  else
    let nd'_name = { nd.n_name with name = prefix ^ "_" ^ nd.n_name.name; } in
    let nd' = pass nd in
    let nd' = { nd' with n_name = nd'_name; } in
    let output = Idents.gen_var "checkpass" "o" in

    let echeck =
      let ty_r = match nd.n_output with
        | [out] -> out.v_type
        | _ -> Tprod (List.map (fun vd -> vd.v_type) nd.n_output) in
      let mk_call nn = mk_exp ~ty:ty_r (Eapp (mk_app (Enode nn), [], None)) in
      mk_exp ~ty:(Tid Initial.pbool) (Eapp (mk_app Eequal, [mk_call nd.n_name; mk_call nd'.n_name], None)) in

    let nd_check =
      mk_node
        ~output:[mk_var_dec output (Tid Initial.pbool)]
        ~eq:[mk_equation (Evarpat output) echeck]
        { nd.n_name with name = prefix ^ "_check_" ^ nd.n_name.name; } in

    let sign = Modules.find_value nd.n_name in
    Modules.add_value nd'.n_name sign;
    Modules.add_value nd_check.n_name
      { node_inputs = [];
        node_outputs = [{ a_name = None; a_type = Tid Initial.pbool; }];
        node_stateful = true;
        node_params = [];
        node_param_constraints = [] };

    Compiler_options.add_assert nd_check.n_name.name;
    nd :: nd' :: nd_check :: nd_list

let add_checks pass prefix nnl p =
  let add nd nd_list =
    if List.mem nd.n_name nnl
    then add_check pass prefix nd nd_list
    else nd :: nd_list in
  { p with p_nodes = List.fold_right add p.p_nodes []; }
