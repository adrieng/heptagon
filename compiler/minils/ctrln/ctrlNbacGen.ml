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
(* Copyright 2013 ENS, INRIA, UJF                                      *)
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

(** Translation from the source language to Controllable-Nbac

    @author Nicolas Berthier *)

(* -------------------------------------------------------------------------- *)

open Signature
open Types
open Names
open Idents
open Minils
open CtrlNbac
open AST

let (&) f g = f g

exception Untranslatable of string                    (* XXX not catched yet! *)

(* --- *)

(** Private record gathering temporary generation data *)
type 'f gen_data =
    {
      typdefs: 'f typdefs;
      decls: 'f node_decls;
      outputs: SSet.t;
      init_cond: 'f bexp;
      init_state: 'f bexp;
      assertion: 'f bexp;
      invariant: 'f bexp;
      (* reachable: bexp; *)
    }

(* --- *)

let tt = mk_bcst' true
let ff = mk_bcst' false
let init_cond_str = "__init__"                             (* XXX uniqueness? *)
and sink_state_str = "__sink__"

let ref_of_typ = function
  | `Bool -> mk_bref
  | `Enum _ -> mk_eref
  | `Int | `Real -> mk_nref

(* --- *)

let translate_constr { name } = mk_label & mk_symb name (* XXX use module name (?) *)
let translate_constrs cl = mk_etyp (List.map translate_constr cl)

(* --- *)

let translate_typ typ = match Modules.unalias_type typ with
  | Tid ({ qual = Pervasives; name = "bool" }) -> `Bool
  | Tid ({ qual = Pervasives; name = "int" }) -> `Int
  | Tid ({ qual = Pervasives; name = "real" }) -> `Real                (* XXX? *)
  | Tid ({ name = tn } as t) -> (match Modules.find_type t with
      | Tenum _ -> `Enum (mk_typname (mk_symb tn))
      | _ -> raise & Untranslatable ("type "^ fullname t))
  | Tprod _ -> raise & Untranslatable ("product type")
  | Tarray _ -> raise & Untranslatable ("array type")
  | Tinvalid -> failwith "Encountered an invalid type!"

(* --- *)

let simplify_static_exp se = (Static.simplify QualEnv.empty se).se_desc

let translate_static_bexp se = match simplify_static_exp se with
  | Sbool true | Sconstructor { qual=Pervasives; name="true" } -> tt
  | Sbool false | Sconstructor { qual=Pervasives; name="false" } -> ff
  | _ -> failwith ("Boolean static expression expected!")

let translate_static_eexp se = match simplify_static_exp se with
  | Sconstructor { qual=Pervasives; name="true" as n }
  | Sconstructor { qual=Pervasives; name="false" as n } ->
      failwith ("Enum static expression expected! (found `"^n^"')")
  | Sconstructor c -> `Enum (translate_constr c)
  | _ -> failwith ("Enum static expression expected!")

let translate_static_nexp se = match simplify_static_exp se with
  | Sint v -> `Int v
  | Sfloat v -> `Real v
  | Sop ({ qual=Pervasives; name="~-" },[{ se_desc=Sint v }]) -> `Int (-v)
  | Sop ({ qual=Pervasives; name="~-." },[{ se_desc=Sfloat v }]) -> `Real (-.v)
  | _ -> failwith ("Numerical static expression expected!")

(* --- *)

let rec translate_ext_bexp ~pref : _ -> 'f bexp = function
  | Wconst se -> translate_static_bexp se
  | Wvar id -> mk_bref' (pref & mk_symb & name id)
  | Wfield _ -> failwith "TODO Unsupported Boolean `field' expression!"
  | Wwhen (ev, _, _) -> translate_ext_bexp ~pref ev.w_desc
  | Wreinit _ -> failwith "TODO Unsupported Boolean `reinit' expression!"

and translate_ext_eexp ~pref : _ -> 'f eexp = function
  | Wconst se -> translate_static_eexp se
  | Wvar id -> mk_eref' (pref & mk_symb & name id)
  | Wwhen (ev, _, _) -> translate_ext_eexp ~pref ev.w_desc
  | _ -> failwith "TODO Unsupported Enum expression!"

and translate_ext_nexp ~pref : _ -> 'f nexp = function
  | Wconst se -> translate_static_nexp se
  | Wvar id -> mk_nref' (pref & mk_symb & name id)
  | Wwhen (ev, _, _) -> translate_ext_nexp ~pref ev.w_desc
  | _ -> failwith "TODO Unsupported Numerical expression!"

let translate_ext ~pref ext = match translate_typ ext.w_ty with
    | `Bool -> `Bexp (translate_ext_bexp ~pref ext.w_desc)
    | `Enum _ -> `Eexp (translate_ext_eexp ~pref ext.w_desc)
    | `Int | `Real -> `Nexp (translate_ext_nexp ~pref ext.w_desc)

(* --- *)

let translate_app ~pref op el =
  let pervasives = function
    | "not",          [e]   -> mk_neg e
    | "or",           e::l  -> mk_disj e l
    | "&",            e::l  -> mk_conj e l
    | "xor",         [e;f]  -> mk_xor e f
    | "=",           [e;f]  -> mk_eq e f
    | "<>",          [e;f]  -> mk_ne e f
    |("<"  | "<."),  [e;f]  -> mk_lt e f
    |("<=" | "<=."), [e;f]  -> mk_le e f
    |(">"  | ">."),  [e;f]  -> mk_gt e f
    |(">=" | ">=."), [e;f]  -> mk_ge e f
    |("+"  | "+."), e::f::l -> mk_sum e f l
    |("-"  | "-."), e::f::l -> mk_sub e f l
    |("*"  | "*."), e::f::l -> mk_mul e f l
    |("/"  | "/."), e::f::l -> mk_div e f l
    | name, _ -> raise (Untranslatable name)
  in
  match op, List.map (translate_ext ~pref) el with
    | Eequal, [e;f] -> mk_eq e f
    | Efun { qual=Pervasives; name }, el -> pervasives (name, el)
    (*  *)
    | Eifthenelse, [c;t;e] -> mk_cond c t e
    | _ -> failwith "Unsupported application!"

(** [translate_exp gd e] translates the {e memoryless} expression [e] into its
    Controllable Nbac representation.  *)
let rec translate_exp ~pref t ({ e_desc = desc; e_ty = ty }) =  (* XXX clock? *)
  let typ = translate_typ ty in assert (t = typ); match desc with
    | Eextvalue ext -> translate_ext ~pref ext
    | Eapp ({ a_op }, el, _) -> translate_app ~pref a_op el
    | Emerge (v, (_c, e) :: l) ->
        let v = pref & mk_symb & name v in
        List.fold_left
          (fun x (c, e) -> mk_cond
            (mk_eq (mk_eref v) (mk_ecst (translate_constr c)))
            (translate_ext ~pref e) x)
          (translate_ext ~pref e)
          l
    | Ewhen (exp, _, _) -> translate_exp ~pref t exp
    | Efby _ -> failwith "TODO: translate_exp (fby)"
    | Estruct _ -> failwith "TODO: translate_exp (struct)"
    | _ -> failwith "TODO: translate_exp"

(* --- *)

let rec translate_clk ~pref on off = function
  | Clocks.Cbase | Clocks.Cvar { contents = Clocks.Cindex _ } -> on
  | Clocks.Cvar { contents = Clocks.Clink ck } -> translate_clk ~pref on off ck
  | Clocks.Con (ck, {name = cstr}, v) ->
      let v = pref & mk_symb & name v in
      let c = mk_eq (mk_eref v) (mk_ecst (mk_label (mk_symb cstr))) in
      translate_clk ~pref (mk_cond c on off) off ck

(* --- *)

let add_state_var gd v typ exp init =
  let mk_init = match typ, init with
    | _,       None   -> (fun b -> b)
    | `Bool,   Some i -> mk_and' (mk_beq' (mk_bref' v) (translate_static_bexp i))
    | `Enum _, Some i -> mk_and' (mk_eeq' (mk_eref' v) (translate_static_eexp i))
    | #ntyp,   Some i -> mk_and' (mk_neq' (mk_nref' v) (translate_static_nexp i))
  in
  { gd with
    decls = SMap.add v (typ, `State (exp, None), None) gd.decls;
    init_state = mk_init gd.init_state; }

let add_output_var gd v typ exp = add_state_var gd v typ exp None

let add_local_var gd v typ exp =
  { gd with decls = SMap.add v (typ, `Local (exp, None), None) gd.decls; }

(* --- *)

let translate_eq ~pref gd ({ eq_lhs = pat;
                             eq_rhs = { e_desc = exp; e_ty = typ } as rhs;
                             eq_base_ck = clk }) =
  let typ = translate_typ typ in
  match pat with
    | Evarpat id ->
        begin
          let v = pref & mk_symb & name id in
          match exp with
            | Efby (init, ev) ->
                let ev = translate_ext ~pref ev in
                let ev = translate_clk ~pref ev (ref_of_typ typ v) clk in
                add_state_var gd v typ ev init
            | _ when SSet.mem v gd.outputs ->
                add_output_var gd v typ (translate_exp ~pref typ rhs)
            | _ ->
                add_local_var gd v typ (translate_exp ~pref typ rhs)
        end
    | Etuplepat _ -> failwith "TODO: Minils.Etuplepat!"

let translate_eqs ~pref = List.fold_left (translate_eq ~pref)

(* --- *)

let prefix_vars ~pref vars : symb -> symb =
  let vars = List.fold_left
    (fun acc { v_ident = id } ->                                (* XXX "_" only? *)
      let v = mk_symb & name id in
      SMap.add v (mk_symb ("_" ^ Symb.to_string v)) acc)
    (SMap.empty) vars
  in
  fun p -> pref (try SMap.find p vars with Not_found -> p)

(** Contract translation *)
let translate_contract ~pref gd
    ({ c_local;           c_eq = equs;
       c_assume = a;      c_enforce = g;
       c_assume_loc = a'; c_enforce_loc = g';
       c_controllables = cl }) =
  let declare_contr decls { v_ident = id; v_type = typ } rank =
    let v = mk_symb & name id in
    SMap.add v (translate_typ typ, `Contr (AST.one, rank, None), None) decls in
  let declare_contrs decls cl =
    fst & List.fold_left
      (fun (decls, rank) c -> (declare_contr decls c rank, AST.succ rank))
      (decls, one) cl
  in

  let pref = prefix_vars ~pref c_local in
  let gd = { gd with decls = declare_contrs gd.decls cl } in
  let gd = translate_eqs ~pref gd equs in
  let ak = as_bexp & mk_and (translate_ext ~pref a) (translate_ext ~pref a')
  and ok = as_bexp & mk_and (translate_ext ~pref g) (translate_ext ~pref g') in

  let gd, ok =
    if !Compiler_options.nosink
    then (gd, ok)
    else let sink = pref & mk_symb sink_state_str in
         let ok = `Bexp (mk_bcond' gd.init_cond tt ok) in
         (add_state_var gd sink `Bool ok None, mk_bref' sink)
  in
  { gd with
    assertion = mk_and' gd.assertion ak;
    invariant = mk_and' gd.invariant ok; }

(* --- *)

(** Node translation. Note the given node is not expored if it does not comprize a
    contract. *)
let translate_node typdefs : 'n -> 'n * (name * 'f AST.node) option = function
  | ({ n_contract = None } as node) -> node, None
  | ({ n_name; n_input; n_output; n_equs; n_contract = Some contr } as node) ->
      let declare_output s { v_ident = id } = SSet.add (mk_symb & name id) s in
      let declare_input decls { v_ident = id; v_type = typ } =
        SMap.add (mk_symb & name id) (translate_typ typ, `Input one, None)
          decls in

      let pref p = p in
      let outputs = List.fold_left declare_output SSet.empty n_output in
      let decls = List.fold_left declare_input SMap.empty n_input in


      let init_cond_var = mk_symb init_cond_str in
      let init_cond = mk_bref' init_cond_var in
      let decls = SMap.add init_cond_var
        (`Bool, `State (`Bexp ff, None), None) decls in
      (* let init_cond = tt in *)

      let gd = { typdefs; decls; outputs;
                 init_cond; init_state = tt;
                 assertion = tt; invariant = tt; } in
      let gd = translate_contract ~pref gd contr in
      let gd = translate_eqs ~pref gd n_equs in

      let ctrln_node_desc = {
        cn_typs = typdefs;
        cn_decls = gd.decls;
        cn_init = mk_and' gd.init_state init_cond;
        cn_assertion = (* mk_or' init_cond  *)gd.assertion;
        cn_invariant = Some (mk_or' init_cond gd.invariant);
        cn_reachable = None;
        cn_attractive = None;
      } in
      node, Some (n_name.name, (`Desc ctrln_node_desc : 'f AST.node))

(* --- *)

(** [gen p] translates all type definitions, plus the nodes comprizing a
    contract, into Controllable-Nbac.

    @return a Controllable-Nbac program comprizing one process for each node
    necessitating controller synthesis), (TODO: and a new Minils program, in
    which those nodes have been transformed so that they "call" their respective
    controller). *)
let gen ({ p_desc = desc } as p) =
  (* Highly insprited by Sigalimain.program. *)

  let _cnp_typs, nodes, descs =
    (* XXX Should we gather all the type definitions before translating any
       node? *)
    List.fold_left begin fun (typdefs, nodes, descs) -> function
      | Pnode n ->
          begin match translate_node typdefs n with
            | node, Some n -> (typdefs, n :: nodes, Pnode node :: descs)
            | node, None -> (typdefs, nodes, Pnode node :: descs)
          end
      | Ptype { t_name = { name }; t_desc = Type_enum cl } ->
          let tn = mk_typname & mk_symb name and typ = translate_constrs cl in
          let typdefs = declare_typ tn typ typdefs in
          (typdefs, nodes, descs)
      | p -> (typdefs, nodes, p :: descs)
    end (empty_typdefs, [], []) desc
  in
  (* let cnp_name = Names.modul_to_string p.p_modname *)
  let cnp_nodes = List.rev nodes and p_desc = List.rev descs in
  cnp_nodes, { p with p_desc }
