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

open Compiler_utils
open Ctrln_utils
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

let tt = mk_bcst' true
let ff = mk_bcst' false

(* --- *)

(** Private record gathering temporary generation data *)
type 'f gen_data =
    {
      typdefs: 'f typdefs;
      decls: 'f node_decls;
      base: (var_ident * ty) SMap.t;
      local: (var_ident * ty) SMap.t;
      contrs: (var_ident * ty) SMap.t;
      output: IdentSet.t;
      init_cond: 'f bexp;
      init_state: 'f bexp;
      assertion: 'f bexp;
      invariant: 'f bexp;
      reachable: 'f bexp option;
      attractive: 'f bexp option;
      remaining_contrs: SSet.t;      (* All controllable inputs that has not yet
                                        been assigned to a U/C group. *)
      local_contr_deps: SSet.t SMap.t;         (* All variables that depend on a
                                                  controllable. *)
      extra_inputs: SSet.t;
      uc_groups: (SSet.t * SSet.t) list;
    }

(* --- *)

let mk_gen_data typdefs decls input local output init_cond =
  {
    typdefs;
    decls;
    base = input;
    local;
    contrs = SMap.empty;
    output;
    remaining_contrs = SSet.empty;
    local_contr_deps = SMap.empty;
    extra_inputs = SSet.empty;
    uc_groups = [];
    init_cond;
    init_state = tt;
    assertion = tt;
    invariant = tt;
    reachable = None;
    attractive = None;
  }

(* --- *)

let translate_constr { name } = mk_label & mk_symb name (* XXX use qual name? *)
let translate_constrs cl = mk_etyp (List.map translate_constr cl)

(* --- *)

let rec translate_typ typ = match Modules.unalias_type typ with
  | Tid ({ qual = Pervasives; name = "bool" }) -> `Bool
  | Tid ({ qual = Pervasives; name = "int" }) -> `Int
  | Tid ({ qual = Pervasives; name = "float" }) -> `Real
  | Tid ({ name = tn } as t) -> (match Modules.find_type t with
      | Tenum _ -> `Enum (mk_typname (mk_symb tn))
      | Talias t -> translate_typ t                                    (* XXX? *)
      | _ -> raise & Untranslatable ("type "^ fullname t))
  | Tprod _ -> raise & Untranslatable ("product type")
  | Tarray _ -> raise & Untranslatable ("array type")
  | Tinvalid -> failwith "Encountered an invalid type!"

let rec fintypp typ = match Modules.unalias_type typ with
  | Tid ({ qual = Pervasives; name = "bool" }) -> true
  | Tid t -> (match Modules.find_type t with
      | Tenum _ -> true
      | Talias t -> fintypp t                                          (* XXX? *)
      | _ -> false)
  | _ -> false

let ref_of_ty ty = match translate_typ ty with
  | `Bool -> mk_bref
  | `Enum _ -> mk_eref
  | `Int | `Real -> mk_nref

(* --- *)

let simplify_static_exp se = (Static.simplify QualEnv.empty se).se_desc

let translate_static_bexp se = match simplify_static_exp se with
  | Sbool true | Sconstructor { qual = Pervasives; name = "true" } -> tt
  | Sbool false | Sconstructor { qual = Pervasives; name = "false" } -> ff
  | _ -> failwith (Format.asprintf "Boolean static expression expected! (found@ \
                    `%a')" Global_printer.print_static_exp se)

let translate_static_eexp se = match simplify_static_exp se with
  | Sconstructor { qual = Pervasives; name = "true" as n }
  | Sconstructor { qual = Pervasives; name = "false" as n } ->
      failwith ("Enum static expression expected! (found `"^n^"')")
  | Sconstructor c -> `Enum (translate_constr c)
  | _ -> failwith (Format.asprintf "Enum static expression expected! (found@ \
                    `%a')" Global_printer.print_static_exp se)

let translate_static_nexp se = match simplify_static_exp se with
  | Sint v -> `Int v
  | Sfloat v -> `Real v
  | Sop ({ qual = Pervasives; name="~-" },[{ se_desc = Sint v }]) -> `Int (-v)
  | Sop ({ qual = Pervasives; name="~-." },[{ se_desc=Sfloat v }]) -> `Real (-.v)
  | _ -> failwith (Format.asprintf "Numerical static expression expected! (found\
                    @ `%a')" Global_printer.print_static_exp se)

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
    |("~-" | "~-."),  [e]   -> mk_opp e
    | "or",           e::l  -> mk_disj e l
    | "&",            e::l  -> mk_conj e l
    | "xor",         [e;f]  -> mk_xor e f
    | "=>",          [e;f]  -> mk_disj (mk_neg e) [f]
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
    | Efun { qual = Pervasives; name }, el -> pervasives (name, el)
    | Eifthenelse, [c;t;e] -> mk_cond c t e
    | _ -> failwith "Unsupported application!"

(** [translate_exp gd e] translates the {e memoryless} expression [e] into its
    Controllable Nbac representation.  *)
let rec translate_exp ~pref ({ e_desc = desc }) =               (* XXX clock? *)
  match desc with
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
    | Ewhen (exp, _, _) -> translate_exp ~pref exp
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

let acc_dependencies_on vars deps_on_vars i e = fold_exp_dependencies
  (fun v s ->
    if SSet.mem v vars then SSet.add v s
    else try SSet.union s (SMap.find v deps_on_vars) with
      | Not_found -> s)
  e i

(* --- *)

let add_state_var' ~pref gd id ty exp init =
  let v = pref & mk_symb & name id in
  let typ = translate_typ ty in
  let mk_init = match typ, init with
    | _,       None   -> (fun b -> b)
    | `Bool,   Some i -> mk_and' (mk_beq' (mk_bref' v) (translate_static_bexp i))
    | `Enum _, Some i -> mk_and' (mk_eeq' (mk_eref' v) (translate_static_eexp i))
    | #ntyp,   Some i -> mk_and' (mk_neq' (mk_nref' v) (translate_static_nexp i))
  in
  { gd with
    decls = SMap.add v (typ, `State (exp, None), None) gd.decls;
    init_state = mk_init gd.init_state; }, v

let add_state_var ~pref gd id ty exp init =
  let gd, v = add_state_var' ~pref gd id ty exp init in
  { gd with base = SMap.add v (id, ty) gd.base; }


(* TODO : add_local_var instead ? (NB : state var used for simulation) *)
let add_output_var ~pref gd id ty exp =
  add_state_var' ~pref gd id ty exp None |> fst

let add_local_var ~pref gd id ty exp =
  let v = pref & mk_symb & name id in
  let typ = translate_typ ty in
  let ldeps = fold_exp_dependencies (fun v acc ->
    if SSet.mem v gd.remaining_contrs then SSet.add v acc
    else try SSet.union acc (SMap.find v gd.local_contr_deps) with
      | Not_found -> acc)
    exp
    SSet.empty
  in
  let local_contr_deps = SMap.add v ldeps gd.local_contr_deps in
  { gd with
    decls = SMap.add v (typ, `Local (exp, None), None) gd.decls;
    local_contr_deps; }

(* TODO : merge with definition above ? *)
let add_output_var ~pref gd id ty exp =
  add_local_var ~pref gd id ty exp

let declare_additional_input ~pref gd id =
  let l = mk_symb & name id in
  try
    let v = pref l in
    let t = SMap.find l gd.local |> snd |> translate_typ in
    { gd with
      decls = SMap.add v (t, `Input one, None) gd.decls;
      extra_inputs = SSet.add v gd.extra_inputs; }
  with
    | Not_found ->                                 (* output of the main node. *)
        assert (IdentSet.mem id gd.output);
        gd

(* --- *)

let close_uc_group gd defined_contrs =
  let rem = SSet.diff gd.remaining_contrs defined_contrs in
  let lcd = SMap.map (SSet.inter rem) gd.local_contr_deps in
  let lcd = SMap.filter (fun _ d -> not (SSet.is_empty d)) lcd in
  { gd with
    remaining_contrs = rem;
    extra_inputs = SSet.empty;
    local_contr_deps = lcd;
    uc_groups = (gd.extra_inputs, defined_contrs) :: gd.uc_groups; }

(* --- *)

let pat_ids pat =
  let rec acc_pat acc = function
    | Evarpat id -> ((* pref &  *)(* mk_symb & name  *)id) :: acc
    | Etuplepat pats -> List.fold_left acc_pat acc pats
  in
  acc_pat [] pat |> List.rev

let translate_abstract_app ~pref gd pat _f args =
  let results = pat_ids (* ~pref *) pat in
  let args = List.map (translate_ext ~pref) args in
  let gd =
    (* in case of dependencies on remainging controllable variables, switch to
       next U/C group. *)
    let depc = List.fold_left
      (acc_dependencies_on gd.remaining_contrs gd.local_contr_deps)
      SSet.empty args
    in
    if SSet.is_empty depc then gd else close_uc_group gd depc
  in
  (* declare extra inputs. *)
  List.fold_left (declare_additional_input ~pref) gd results

(* --- *)


let translate_eq ~pref (gd, equs)
    ({ eq_lhs = pat;
       eq_rhs = { e_desc = exp; e_ty = ty } as rhs;
       eq_base_ck = clk } as eq)
    =
  let abstract_infinite_state = !Compiler_options.abstract_infinite in
  match pat with
    | Evarpat id ->
        begin match exp with
          | Efby _ when (abstract_infinite_state && not (fintypp ty)) ->
              warn ~cond:(!Compiler_options.warn_abstractions)
                "Abstracting@ %a@ state@ variable@ %s@ as@ non-controllable@ \
                 input." Global_printer.print_type ty (name id);
              (declare_additional_input ~pref gd id, eq :: equs)
          | Efby (init, ev) ->
              let v = pref & mk_symb & name id in
              let ev = translate_ext ~pref ev in
              let ev = translate_clk ~pref ev (ref_of_ty ty v) clk in
              (add_state_var ~pref gd id ty ev init, eq :: equs)
          | Eapp ({ a_op = (Enode f | Efun f) }, args, None) (* TODO : handle resets *)
                when f.qual <> Pervasives ->
              (translate_abstract_app ~pref gd pat f args, eq :: equs)
          | _ when IdentSet.mem id gd.output ->
              let exp = translate_exp ~pref rhs in
              (add_output_var ~pref gd id ty exp, eq :: equs)
          | _ ->
              let exp = translate_exp ~pref rhs in
              (add_local_var ~pref gd id ty exp, eq :: equs)
        end
    | Etuplepat _ ->
        begin match exp with
          | Eapp ({ a_op = (Enode f | Efun f) }, args, None) (* TODO : handle resets *)
                when f.qual <> Pervasives ->
              (translate_abstract_app ~pref gd pat f args, eq :: equs)
          | _ -> failwith "TODO: Minils.Etuplepat construct!"
        end

let translate_eqs ~pref acc equs =
  let gd, equs = List.fold_left (translate_eq ~pref) acc equs in
  gd, List.rev equs

(* --- *)

let prefix_vars ~pref vars : symb -> symb =
  let vars = List.fold_left begin fun acc { v_ident = id } ->
    let v = mk_symb & name id in
    SMap.add v (mk_symb (Symb.to_string v)) acc
  end (SMap.empty) vars in
  fun p -> pref (try SMap.find p vars with Not_found -> p)

let declare_contr (decls, contrs, vds)
    ({ v_ident = id; v_type = ty } as vd) rank =
  let v = mk_symb & name id in
  SMap.add v (translate_typ ty, `Contr (one, rank, `None), None) decls,
  SMap.add v (id, ty) contrs,
  vd :: vds

let declare_contrs acc cl =
  fst & List.fold_left
    (fun (acc, rank) c -> (declare_contr acc c rank, AST.succ rank))
    (acc, one) cl

(** Contract translation *)
let translate_contract ~pref gd
    ({ c_local;           c_eq = equs;
       c_assume = a;      c_objectives = objs;
       c_assume_loc = a'; c_enforce_loc = g';
       c_controllables = cl } as contract)
    =
  let pref = prefix_vars ~pref c_local in
  let decls, contrs, locals = declare_contrs (gd.decls, SMap.empty, []) cl in
  let c = SMap.fold (fun v _ -> SSet.add v) contrs SSet.empty in
  let gd = { gd with decls; contrs; remaining_contrs = c; } in
  let gd, equs' = translate_eqs ~pref (gd, []) equs in
  let ak = as_bexp & mk_and (translate_ext ~pref a) (translate_ext ~pref a')
  and ok = as_bexp & translate_ext ~pref g' in

  let gd = { gd with
             assertion = mk_and' gd.assertion ak;
             invariant = mk_and' gd.invariant ok; } in

  let opt_and opt_e e' =
    match opt_e with
      None -> Some e'
    | Some e -> Some (mk_and' e e') in

  let add_objective gd o =
    let e = as_bexp & translate_ext ~pref o.o_exp in
    match o.o_kind with
    | Obj_enforce -> { gd with invariant = mk_and' gd.invariant e; }
    | Obj_reachable -> { gd with reachable = opt_and gd.reachable e; }
    | Obj_attractive -> { gd with attractive = opt_and gd.attractive e; } in

  let gd = List.fold_left add_objective gd objs in

  (gd, { contract with c_eq = equs'; }, locals)

(* --- *)

let declare_output s { v_ident = id } =
  IdentSet.add id s

let declare_input m { v_ident = id; v_type = typ } =
  SMap.add (mk_symb & name id) (translate_typ typ, `Input one, None) m

let register_var_typ m { v_ident = id; v_type = typ } =
  SMap.add (mk_symb & name id) (id, typ) m

(* --- *)

let finalize_uc_groups gd =
  let gd = if SSet.is_empty gd.remaining_contrs then gd else
      (* switch to last U/C group here, and declare controller call. *)
      close_uc_group gd gd.remaining_contrs
  in
  if SSet.is_empty gd.extra_inputs then gd else
    { gd with
      extra_inputs = SSet.empty;
      uc_groups = (gd.extra_inputs, SSet.empty) :: gd.uc_groups; }

(* Note uc_groups are reversed in gd BEFORE the call to this function. *)
let assign_uc_groups gd =
  let gd = finalize_uc_groups gd in
  let uc_groups = List.rev gd.uc_groups in      (* start from the first group *)
  let decls, _ =
    if uc_groups = [] then
      gd.decls, one                                     (* no group to change *)
    else
      List.fold_left begin fun (decls, group) (u, c) ->
        let decls = SSet.fold (fun u decls -> match SMap.find u decls with
          | (t, `Input _, l) ->
              SMap.add u (t, `Input group, l) decls
          | _ -> decls) u decls
        in
        let decls = SSet.fold (fun c decls -> match SMap.find c decls with
          | (t, `Contr (_, r, l'), l) ->
              SMap.add c (t, `Contr (group, r, l'), l) decls
          | _ -> decls) c decls
        in
        decls, AST.succ group
      end (gd.decls, AST.succ one) (List.tl uc_groups)
  in
  { gd with decls; uc_groups }

(* --- *)

let scmp a b = String.compare (Symb.to_string a) (Symb.to_string b)

let var_exp v ty =
  mk_extvalue ~ty ~clock:Clocks.Cbase ~linearity:Linearity.Ltop (Wvar v)

let decl_arg (v, t) =
  mk_arg (Some (name v)) t Linearity.Ltop Signature.Cbase

let gen_ctrlf_calls ~requal_types gd node_name equs =

  let equs, _, _ = List.fold_left begin fun (equs, ubase, num) (u, c) ->

    (* Controllable inputs of the current U/C group *)
    let c = SSet.elements c in
    let c = List.sort scmp c in                       (* XXX now optional (x) *)
    let o = List.map (fun v -> SMap.find v gd.contrs) c in
    let os = List.map decl_arg o in
    let ov, ot = List.split o in
    let ov = Etuplepat (List.map (fun v -> Evarpat v) ov) in

    (* Accumulate state variables and all non-controllable inputs from the
       beginning, plus all controllables from previous U/C groups *)
    let u = SSet.fold (fun v -> SMap.add v (SMap.find v gd.local)) u ubase in
    let i = SMap.bindings u in
    let i = List.sort (fun (a, _) (b, _) -> scmp b a) i in  (* rev. i + ibid (x) *)
    let is = List.rev_map (fun (_, p) -> decl_arg p) i in
    let i = List.rev_map (fun (_, (v, t)) -> var_exp v t) i in

    (* Build controller call *)
    let func_name = controller_node ~num node_name in
    let app = Eapp (mk_app (Efun func_name), i, None) in
    let exp = mk_exp ~linearity:Linearity.Ltop Clocks.Cbase (Tprod ot) app in
    let equ = mk_equation false ov exp in

    let is, os = if requal_types then
        (* Optional requalification of types declared in the exported module: *)
        let requal_arg = function
          | { a_type = Tid { qual; name } } as arg when qual = node_name.qual ->
              { arg with a_type = Tid { qual = func_name.qual; name } }
          | a -> a
        in
        List.map requal_arg is, List.map requal_arg os
      else
        is, os
    in

    (* Declare new node *)
    let node_sig = Signature.mk_node Location.no_location ~extern:false is os
      false false [] in
    Modules.add_value func_name node_sig;

    (* Augment base non-controllble inputs with current controllables *)
    let u = List.fold_left (fun u v -> SMap.add v (SMap.find v gd.contrs) u) u c in

    (equ :: equs, u, num + 1)
  end (equs, gd.base, 0) gd.uc_groups in

  equs

(* --- *)

(** Node translation. Note the given node is not expored if it does not comprize a
    contract. *)
let translate_node ~requal_types typdefs = function
  | ({ n_contract = None } as node) -> node, None
  | ({ n_name; n_params } as node) when n_params <> [] ->
      warn ~cond:(!Compiler_options.warn_untranslatable)
        "Unsupported@ translation@ of@ parametric@ node@ `%s'@ with@ \
         contract@ into@ Controllable-Nbac!" (Names.fullname n_name);
      node, None
  | ({ n_name; n_input; n_output; n_local; n_equs;
       n_contract = Some contr } as node) ->

      enter_node n_name;              (* for optional sink symbol generation. *)

      let pref p = p in
      let local = List.fold_left register_var_typ SMap.empty n_local in
      let input = List.fold_left register_var_typ SMap.empty n_input in
      let output = List.fold_left declare_output IdentSet.empty n_output in
      let decls = List.fold_left declare_input SMap.empty n_input in

      let init_cond_var = mk_symb init_cond_str in
      let init_cond = mk_bref' init_cond_var in    (* XXX what about gd.base? *)
      let init_cond_spec = (`Bool, `State (`Bexp ff, None), None) in
      let decls = SMap.add init_cond_var init_cond_spec decls in

      let gd = mk_gen_data typdefs decls input local output init_cond in
      let gd, contract, locals' = translate_contract ~pref gd contr in
      let gd, equs' = translate_eqs ~pref (gd, []) n_equs in
      let gd = assign_uc_groups gd in
      let equs' = gen_ctrlf_calls ~requal_types gd n_name equs' in

      (* Sink state *)
      let sink_state_var = mk_symb sink_state_str in
      let sink_state = mk_bref' sink_state_var in
      let sink_state_spec = (`Bool, `State (`Bexp gd.invariant, None), None) in
      let gd = {gd with decls = SMap.add sink_state_var sink_state_spec gd.decls } in

      let ctrln_node_desc =
        { cn_typs = typdefs;
          cn_decls = gd.decls;
          cn_init = mk_and' (mk_and' gd.init_state init_cond) sink_state;
          cn_assertion = (* mk_or' init_cond  *)gd.assertion;
          cn_invariant = Some (mk_or' init_cond sink_state);
          cn_reachable = gd.reachable;
          cn_attractive = gd.attractive; }
      and node =
        { node with
          n_equs = equs';
          n_local = List.rev_append locals' n_local;
          n_contract = Some contract; }
      in

      (node, Some (n_name, (`Desc ctrln_node_desc : 'f AST.node)))

(* --- *)

(** Moves all type declarations into the given module, declare aliases for them
    (in cases). Also requalifies constructor names in the program, as well as
    types of expressions to avoid some errors in code generation later on. *)
let requal_declared_types prog =

  let cmodul = types_modul prog.p_modname in
  let requal m = m = prog.p_modname in

  let requal_constr ({ qual; name } as cstr) =
    if requal qual then { qual = cmodul; name } else cstr in

  let requal_type = function               (* requalify enum and alias types. *)
    | Tid ({ qual; name } as ty) as t when requal qual ->
        (match Modules.find_type ty with
          | Tenum _ | Talias _ -> Tid { qual = cmodul; name }
          | _ -> t)
    | t -> t
  in

  let requal_type_dec = function
    | { t_name = tn; t_desc } as t when requal tn.qual ->
        let new_type = match t_desc with
          | Type_enum cl -> Signature.Tenum (List.map requal_constr cl)
          | Type_alias t -> Signature.Talias (requal_type t)
          | _ -> raise Errors.Fallback
        in
        let tn' = { tn with qual = cmodul } in
        let t = { t with t_name = tn; t_desc = Type_alias (Tid tn') } in
        Modules.replace_type tn (Signature.Talias (Tid tn'));
        Modules.add_type tn' new_type;
        t
    | _ -> raise Errors.Fallback
  in

  let open Mls_mapfold in
  let open Global_mapfold in
  let funcs = { Mls_mapfold.defaults with

    type_dec = (fun _ () td -> requal_type_dec td, ());

    edesc = (fun funs () -> function
      | Ewhen (e, c, x) ->
          Ewhen (exp_it funs () e |> fst, requal_constr c,
                 var_ident_it funs.global_funs () x |> fst), ()
      | Emerge (i, l) ->
          Emerge (var_ident_it funs.global_funs () i |> fst,
                  List.map (fun (c, x) -> requal_constr c,
                    extvalue_it funs () x |> fst) l), ()
      | _ -> raise Errors.Fallback);

    extvalue_desc = (fun funs () -> function
      | Wwhen (w, c, v) ->
          Wwhen (extvalue_it funs () w |> fst, requal_constr c,
                 var_ident_it funs.global_funs () v |> fst), ()
      | _ -> raise Errors.Fallback);

    global_funs = { Global_mapfold.defaults with

      ty = (fun _ () ty -> requal_type ty, ());

      ck = (fun funs () -> function
        | Clocks.Con (ck, c, i) ->
            Clocks.Con (ck_it funs () ck |> fst, requal_constr c,
                        var_ident_it funs () i |> fst), ()
        | _ -> raise Errors.Fallback);

      static_exp_desc = (fun _ () -> function
        | Sconstructor c -> Sconstructor (requal_constr c), ()
        | _ -> raise Errors.Fallback);

    };
  } in

  program funcs () prog |> fst

(* --- *)

(** [gen p] translates all type definitions, plus the nodes comprizing a
    contract, into Controllable-Nbac.

    @return a Controllable-Nbac program comprizing one process for each node
    necessitating controller synthesis), and a new Minils program, in which
    those nodes have been transformed so that they "call" their respective
    controller.

    XXX The [requalify_declared_types] argument is here to avoid cyclic
    dependencies between modules due to type declarations. Yet, a better idea
    might be to integrate the generated controllers into the original program
    later on.  *)
let gen ?(requalify_declared_types = false) ({ p_desc } as p) =

  let requal_types = requalify_declared_types in

  let _cnp_typs, nodes, descs =
    List.fold_left begin fun (typdefs, nodes, descs) -> function
      | Pnode n ->
          begin match translate_node ~requal_types typdefs n with
            | node, Some n -> (typdefs, n :: nodes, Pnode node :: descs)
            | node, None -> (typdefs, nodes, Pnode node :: descs)
          end
      | Ptype { t_name = ({ name }); t_desc = Type_enum cl } as ty ->
          let tn = mk_typname & mk_symb name and typ = translate_constrs cl in
          let typdefs = declare_typ tn typ typdefs in
          (typdefs, nodes, ty :: descs)
      | p -> (typdefs, nodes, p :: descs)
    end (empty_typdefs, [], []) p_desc
  in

  let cnp_nodes = List.rev nodes
  and p_desc = List.rev descs in
  let prog = { p with p_desc } in
  let prog =
    if requalify_declared_types
    then requal_declared_types prog
    else prog
  in
  cnp_nodes, prog
