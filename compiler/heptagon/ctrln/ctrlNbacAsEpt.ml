(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(* Nicolas Berthier, SUMO, INRIA                                       *)
(*                                                                     *)
(* Copyright 2014 ENS, INRIA, UJF                                      *)
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

open Types
open Names
open Idents
open Heptagon
open CtrlNbac
open AST

exception Untranslatable of string * Loc.t option

(* --- *)

(** Private record gathering temporary generation data *)
type 'f gen_data =
    {
      decls: ('f, 'f var_spec) decls;
      ltyps: (typ * 'f option) SMap.t;
      qname: string -> qualname;
      mutable tdefs: type_name SMap.t;
      mutable env: var_dec Env.t;
      mutable var_names: ident SMap.t;
    }

(* --- *)

let mk_gen_data _module_name decls typdefs =
  {
    decls;
    ltyps = label_typs typdefs;
    qname = (fun name -> { qual = (* Module module_name *)LocalModule; name });
    tdefs = SMap.empty;
    env = Env.empty;
    var_names = SMap.empty;
  }

(* --- *)

let opt_decl_loc gd v = match SMap.find v gd.decls with | _, _, loc -> loc

let translate_typ gd vdecl = function
  | `Bool -> Initial.tbool
  | `Int -> Initial.tint
  | `Real -> Initial.tfloat
  | `Enum tn -> Tid (SMap.find tn gd.tdefs)
  | t -> raise (Untranslatable (Format.asprintf "type %a" print_typ t,
                               opt_decl_loc gd vdecl))

let symb_typ gd s = try match SMap.find s gd.decls with | typ, _, _ -> typ with
  | Not_found -> fst (SMap.find s gd.ltyps)

let symb_typ' gd s = translate_typ gd s (symb_typ gd s)

let translate_label gd l = gd.qname (Symb.to_string (label_symb l))

let ts gd v = SMap.find v gd.var_names

let pat_of_var gd v = Evarpat (ts gd v)

(* --- *)

let mkp t e =
  {
    e_desc = e;
    e_ty = t;
    e_ct_annot = None;
    e_level_ck = Clocks.Cbase;
    e_linearity = Linearity.Ltop;
    e_loc = Location.no_location;
  }

let mkb = mkp Initial.tbool

let mk_app op =
  {
    a_op = op;
    a_params = [];
    a_unsafe = false;                                                  (* ??? *)
    a_inlined = true;                                                  (* ??? *)
  }

let mk_uapp op e = Eapp (mk_app op, [e] , None)
let mk_bapp op e f = Eapp (mk_app op, [e; f] , None)
let mk_ite c t e = Eapp (mk_app Eifthenelse, [c; t; e] , None)

let apptyp = function
  | Eapp ({ a_op = Eifthenelse }, _ :: { e_ty } :: _, _) -> e_ty
  | _ -> assert false

let eqrel: eqrel -> fun_name = function
  | `Eq -> Initial.mk_pervasives "="
  | `Ne -> Initial.mk_pervasives "<>"

let nuop t : nuop -> fun_name = function
  | `Opp when t = Initial.tfloat -> Initial.mk_pervasives "~-."
  | `Opp -> Initial.mk_pervasives "~-"

let nnop t : nnop -> fun_name = function
  | `Sum when t = Initial.tfloat -> Initial.mk_pervasives "+."
  | `Sub when t = Initial.tfloat -> Initial.mk_pervasives "-."
  | `Mul when t = Initial.tfloat -> Initial.mk_pervasives "*."
  | `Div when t = Initial.tfloat -> Initial.mk_pervasives "/."
  | `Sum -> Initial.mk_pervasives "+"
  | `Sub -> Initial.mk_pervasives "-"
  | `Mul -> Initial.mk_pervasives "*"
  | `Div -> Initial.mk_pervasives "/"

let buop: buop -> fun_name = function
  | `Neg -> Initial.pnot

let bnop: bnop -> fun_name = function
  | `Conj -> Initial.pand
  | `Disj -> Initial.por
  | `Excl -> failwith "TODO: translation of exclusion operator"

let translate_expr gd e =
  let mkb_bapp_eq ?flag tr e f l =
    let e = tr ?flag e in
    let mkcmp a b = mkb (mk_bapp (Efun (eqrel `Eq)) a b) in
    let mkcmp' f = mkcmp e (tr ?flag f) in
    let disj = mk_bapp (Efun Initial.por) in
    List.fold_left (fun acc f -> mkb (disj acc (mkcmp' f))) (mkcmp' f) l
  and mkb_bapp ?flag op tr e f l =
    let op = mk_bapp op in
    List.fold_left (fun acc e -> mkb (op acc (tr ?flag e))) (tr ?flag e) (f::l)
  and trcond ?flag tb tr = ignore flag; function
    | `Ite (c, t, e) -> let e = mk_ite (tb c) (tr t) (tr e) in mkp (apptyp e) e
  in

  let rec tb ?flag = function
    | `Ref v -> mkb (Evar (ts gd v))
    | `Bool b -> mkb (Econst (Initial.mk_static_bool b))
    | `Buop (op, e) -> mkb (mk_uapp (Efun (buop op)) (tb e))
    | `Bnop (op, e, f, l) -> mkb_bapp ?flag (Efun (bnop op)) tb e f l
    | `Bcmp (re, e, f) -> mkb (mk_bapp (Efun (eqrel re)) (tb e) (tb f))
    | `Ncmp _ -> assert false
    | `Ecmp (re, e, f) -> mkb (mk_bapp (Efun (eqrel re)) (te e) (te f))
    | `Pcmp (re, e, f) -> mkb (mk_bapp (Efun (eqrel re)) (tp e) (tp f))
    | `Pin (e, f, l) -> mkb_bapp_eq ?flag tp e f l
    | `Bin (e, f, l) -> mkb_bapp_eq ?flag tb e f l
    | `Ein (e, f, l) -> mkb_bapp_eq ?flag te e f l
    | `BIin _ -> assert false
    | #cond as c -> trcond ?flag tb tb c
    | #flag as e -> apply' tb e
  and te ?flag = ignore flag; function
    | `Ref v -> mkp (symb_typ' gd v) (Evar (ts gd v))
    | `Enum l -> let s = label_symb l in
                let t = symb_typ' gd s in
                let c = gd.qname (Symb.to_string s) in
                mkp t (Econst (mk_static_exp t (Sconstructor c)))
    | #cond as c -> trcond ?flag tb te c
    | #flag as e -> apply' te e
  and tn ?flag = function
    | `Ref v -> mkp (symb_typ' gd v) (Evar (ts gd v))
    | `Int i -> mkp Initial.tint (Econst (Initial.mk_static_int i))
    | `Real r -> mkp Initial.tfloat (Econst (Initial.mk_static_float r))
    | `Mpq r -> tn ?flag (`Real (Mpqf.to_float r))
    | `Bint _ -> assert false
    | `Nuop (op, e) -> mk_nuapp ?flag op e
    | `Nnop (op, e, f, l) -> mk_nnapp ?flag op e f l
    | #cond as c -> trcond ?flag tb tn c
    | #flag as e -> apply' tn e
  and mk_nuapp ?flag op e =
    let { e_ty } as e = tn ?flag e in
    mkp e_ty (mk_uapp (Efun (nuop e_ty op)) e)
  and mk_nnapp ?flag op e f l =
    let { e_ty } as e = tn ?flag e in
    let op = mk_bapp (Efun (nnop e_ty op)) in
    List.fold_left (fun acc e -> mkp e_ty (op acc (tn ?flag e))) e (f::l)
  and tp ?flag : 'f AST.exp -> _ = function
    | `Bexp e -> tb ?flag e
    | `Eexp e -> te ?flag e
    | `Nexp e -> tn ?flag e
    | `Ref v -> (match symb_typ gd v with
        | `Enum _ -> te ?flag (`Enum (mk_label v))
        | t -> mkp (translate_typ gd v t) (Evar (ts gd v)))
    | #cond as c -> trcond ?flag tb tp c
    | #flag as e -> apply' tp e
  in
  tp e

(* --- *)

let decl_typs typdefs gd =
  fold_typdefs begin fun tname tdef typs ->
    let name = gd.qname (Symb.to_string tname |> String.uncapitalize) in
    match tdef with
      | EnumDef labels ->
          let constrs = List.map (fun (l, _) -> translate_label gd l) labels in
          gd.tdefs <- SMap.add tname name gd.tdefs;
          { t_name = name;
            t_desc = Type_enum constrs;
            t_loc = Location.no_location }:: typs
  end typdefs []

(* --- *)

let decl_var_acc gd v t acc =
  let ident = ident_of_name (Symb.to_string v) in
  let vd = {
    v_ident = ident;
    v_type = translate_typ gd v t;
    v_linearity = Linearity.Ltop;
    v_clock = Clocks.Cbase;
    v_last = Var;
    v_loc = Location.no_location;
  } in
  gd.env <- Env.add ident vd gd.env;
  gd.var_names <- SMap.add v ident gd.var_names;
  vd :: acc

(* --- *)

let translate_equ_acc gd v e acc =
  {
    eq_desc = Eeq (pat_of_var gd v, translate_expr gd e);
    eq_stateful = false;                                               (* ??? *)
    eq_inits = Linearity.Lno_init;
    eq_loc = Location.no_location;       (* first-level flag of e: (flagof e) *)
  } :: acc

(* --- *)

let block_of_func gd { fni_local_vars; fni_all_specs } =
  let locals = SMap.fold (decl_var_acc gd) fni_local_vars [] in
  let equs = SMap.fold (translate_equ_acc gd) fni_all_specs [] in
  {
    b_local = locals;
    b_equs = List.rev equs;                             (* for readability... *)
    b_defnames = gd.env;
    b_stateful = false;
    b_loc = Location.no_location;
  }

(* --- *)

let scmp a b = String.compare (Symb.to_string a) (Symb.to_string b)
let io_of_func gd { fni_io_vars } =
  let i, o = List.fold_left (fun (i, o) { fnig_input_vars; fnig_output_vars } ->
    (List.rev_append (SMap.bindings fnig_input_vars) i,
     List.rev_append (SMap.bindings fnig_output_vars) o)) ([], []) fni_io_vars
  in
  let i = List.sort (fun (a, _) (b, _) -> scmp b a) i in                 (* rev. *)
  let i = List.fold_left (fun acc (v, t) -> decl_var_acc gd v t acc) [] i in
  let o = List.sort (fun (a, _) (b, _) -> scmp b a) o in                 (* rev. *)
  let o = List.fold_left (fun acc (v, t) -> decl_var_acc gd v t acc) [] o in
  i, o

(* --- *)

let node_of_func gd func =
  let n_name = gd.qname "func" in
  enter_node n_name;
  let fi = gather_func_info func in
  let n_input, n_output = io_of_func gd fi in
  let block = block_of_func gd fi in
  {
    n_name;
    n_stateful = false;                                                (* ??? *)
    n_unsafe = false;                                                  (* ??? *)
    n_input;
    n_output;
    n_contract = None;                                             (* <- TODO *)
    n_block = block;
    n_loc = Location.no_location;
    n_params = [];
    n_param_constraints = [];
  }

(* --- *)

let gen_func ~module_name func =
  let { fn_typs; fn_decls } = func_desc func in
  let gd = mk_gen_data module_name (fn_decls:> ('f, 'f var_spec) decls) fn_typs in
  let typs = decl_typs fn_typs gd in
  let typs = List.rev_map (fun t -> Ptype t) typs in
  let node = node_of_func gd func in
  {
    p_modname = Module module_name;
    p_opened = [];
    p_desc = List.rev (Pnode node :: typs);
  }
