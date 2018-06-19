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

open Format
open Signature
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
      typ_symbs: type_name SMap.t;
      mutable env: var_dec Env.t;
      mutable var_names: ident SMap.t;
    }

let no_typ_symbs: type_name SMap.t = SMap.empty

(* --- *)

let mk_gen_data qualname typ_symbs decls typdefs =
  {
    decls;
    ltyps = label_typs typdefs;
    qname = (fun name -> { qual = modul qualname; name });
    typ_symbs;
    env = Env.empty;
    var_names = SMap.empty;
  }

(* --- *)

let opt_decl_loc gd v = match SMap.find v gd.decls with | _, _, loc -> loc

let translate_typ gd vdecl = function
  | `Bool -> Initial.tbool
  | `Int -> Initial.tint
  | `Real -> Initial.tfloat
  | `Enum tn -> Tid (SMap.find tn gd.typ_symbs)
  | t -> raise (Untranslatable (asprintf "type %a" print_typ t,
                               opt_decl_loc gd vdecl))

let symb_typ gd s = try match SMap.find s gd.decls with | typ, _, _ -> typ with
  | Not_found -> fst (SMap.find s gd.ltyps)

let symb_typ' gd s = translate_typ gd s (symb_typ gd s)

let ts gd v = try SMap.find v gd.var_names with Not_found ->
  failwith (asprintf "Variable name `%a' unavailable; \
                      was it an output of the main node?" Symb.print v)

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

let float_typ t = Modules.unalias_type t = Initial.tfloat

let totrel t : totrel -> fun_name =
  if float_typ t
  then function
    | `Lt -> Initial.mk_pervasives "<."
    | `Le -> Initial.mk_pervasives "<=."
    | `Gt -> Initial.mk_pervasives ">."
    | `Ge -> Initial.mk_pervasives ">=."
    | #eqrel as r -> eqrel r
  else function
    | `Lt -> Initial.mk_pervasives "<"
    | `Le -> Initial.mk_pervasives "<="
    | `Gt -> Initial.mk_pervasives ">"
    | `Ge -> Initial.mk_pervasives ">="
    | #eqrel as r -> eqrel r

let nuop t : nuop -> fun_name =
  if float_typ t
  then function
    | `Opp -> Initial.mk_pervasives "~-."
  else function
    | `Opp -> Initial.mk_pervasives "~-"

let nnop t : nnop -> fun_name =
  if float_typ t
  then function
    | `Sum -> Initial.mk_pervasives "+."
    | `Sub -> Initial.mk_pervasives "-."
    | `Mul -> Initial.mk_pervasives "*."
    | `Div -> Initial.mk_pervasives "/."
  else function
    | `Sum -> Initial.mk_pervasives "+"
    | `Sub -> Initial.mk_pervasives "-"
    | `Mul -> Initial.mk_pervasives "*"
    | `Div -> Initial.mk_pervasives "/"

let buop: buop -> fun_name = function
  | `Neg -> Initial.pnot

let bbop: bbop -> fun_name = function
  | `Imp -> Initial.pimp

let bnop: bnop -> fun_name = function
  | `Conj -> Initial.pand
  | `Disj -> Initial.por
  | `Excl -> failwith "TODO: translation of exclusion operator"

(* --- *)

let rec flttyp_exp ({ e_desc; e_ty } as e) =
  if e_ty = Initial.tfloat then e
  else { e with e_ty = Initial.tfloat; e_desc = flttyp_desc e_desc }
and flttyp_desc = function
  | Econst s -> Econst (flttyp_sexp s)
  | Eapp ({ a_op = Efun { qual = Pervasives; name } } as op, el, None) ->
      (* NB: very hackish stuff *)
      begin match name with
        | "+" | "-" | "*" | "/" | "~-" ->
            let a_op = Efun (Initial.mk_pervasives (name^".")) in
            Eapp ({ op with a_op }, List.map flttyp_exp el, None)
        | _ -> assert false
      end
  | Evar v -> Evar v
  | _ -> assert false
and flttyp_sexp ({ se_desc; se_ty } as e) =
  if se_ty = Initial.tfloat then e
  else { e with se_ty = Initial.tfloat; se_desc = flttyp_sdesc se_desc }
and flttyp_sdesc = function
  | Sint i -> Sfloat (float_of_int i)
  | _ -> assert false

(* --- *)

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
    | `Bbop (op, e, f) -> mkb (mk_bapp (Efun (bbop op)) (tb e) (tb f))
    | `Bnop (op, e, f, l) -> mkb_bapp ?flag (Efun (bnop op)) tb e f l
    | `Bcmp (re, e, f) -> mkb (mk_bapp (Efun (eqrel re)) (tb e) (tb f))
    | `Ecmp (re, e, f) -> mkb (mk_bapp (Efun (eqrel re)) (te e) (te f))
    | `Pcmp (re, e, f) -> mkb (mk_bapp (Efun (eqrel re)) (tp e) (tp f))
    | `Ncmp (re, e, f) -> mkb_ncmp re e f
    | `Pin (e, f, l) -> mkb_bapp_eq ?flag tp e f l
    | `Bin (e, f, l) -> mkb_bapp_eq ?flag tb e f l
    | `Ein (e, f, l) -> mkb_bapp_eq ?flag te e f l
    | `BIin _ -> raise (Untranslatable ("bounded Integer membership", flag))
    | #cond as c -> trcond ?flag tb tb c
    | #flag as e -> apply' tb e
  and te ?flag = function
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
    | `Nuop (op, e) -> mk_nuapp ?flag op e
    | `Nnop (op, e, f, l) -> mk_nnapp ?flag op e f l
    | `Ncst _ -> raise (Untranslatable ("Cast operation", flag))
    | `Luop _
    | `Lbop _
    | `Lsop _ -> raise (Untranslatable ("Bitwise operation", flag))
    | #cond as c -> trcond ?flag tb tn c
    | #flag as e -> apply' tn e
  and mkb_ncmp ?flag re e f =
    let { e_ty = et } as e = tn ?flag e
    and { e_ty = ft } as f = tn ?flag f in
    (* NB: these coercions may not be needed, but let's keep it in case *)
    if et = Initial.tfloat && ft = Initial.tint
    then mkb (mk_bapp (Efun (totrel et re)) e (flttyp_exp f))
    else if et = Initial.tint && ft = Initial.tfloat
    then mkb (mk_bapp (Efun (totrel ft re)) (flttyp_exp e) f)
    else mkb (mk_bapp (Efun (totrel et re)) e f)
  and mk_nuapp ?flag op e =
    let { e_ty } as e = tn ?flag e in
    mkp e_ty (mk_uapp (Efun (nuop e_ty op)) e)
  and mk_nnapp ?flag op e f l =
    let el = List.rev_map (tn ?flag) (e :: f :: l) in
    (* NB: manual coercion from ints to floats *)
    let flt = List.exists (fun { e_ty } -> e_ty = Initial.tfloat) el in
    let typ = if flt then Initial.tfloat else Initial.tint in
    let el = if flt
      then List.rev_map flttyp_exp el
      else List.rev el in
    let op = mk_bapp (Efun (nnop typ op)) in
    List.fold_left (fun acc e -> mkp typ (op acc e)) (List.hd el) (List.tl el)
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

let decl_typs modul_name typdefs =
  let qualify name = { qual = modul modul_name; name } in
  fold_typdefs begin fun tname tdef (types, typ_symbs) ->
    let name = qualify (Symb.to_string tname |> String.uncapitalize_ascii) in
    match tdef with
      | EnumDef labels, _ ->
          let constrs = List.map (fun (l, _) ->
            qualify (Symb.to_string (label_symb l))) labels in
          (Ptype { t_name = name;
                   t_desc = Type_enum constrs;
                   t_loc = Location.no_location } :: types,
           SMap.add tname name typ_symbs)
  end typdefs ([], no_typ_symbs)

let decl_typs_from_module_itf modul_name =
  (* Note we need to sort type declarations according to their respective
     dependencies; hence the implicit topological traversal of the type
     definitions. *)
  let rec decl_types rem acc =
    if QualEnv.is_empty rem then
      acc
    else
      let t_name, tdef = QualEnv.choose rem in
      let rem, acc = decl_typ t_name tdef rem acc in
      decl_types rem acc
  and decl_typ t_name tdef rem ((types, typ_symbs) as acc) =
    let rem = QualEnv.remove t_name rem in
    if t_name.qual <> modul_name then
      rem, acc
    else
      let t_desc, rem, (types, typ_symbs) = match tdef with
        | Tenum cl ->
            (* Compiler_utils.info "declaring enum type %s" (shortname t_name); *)
            let name = Symb.of_string (String.capitalize_ascii (shortname t_name)) in
            (Type_enum cl, rem, (types, SMap.add name t_name typ_symbs))
        | Talias (Tid tn) when tn.qual = t_name.qual ->    (* declare deps 1st *)
            (* Compiler_utils.info "declaring alias type %s" (shortname t_name); *)
            let tdef = QualEnv.find tn rem in
            let rem, acc = decl_typ tn tdef (QualEnv.remove tn rem) acc in
            (Type_alias (Tid tn), rem, acc)
        | Talias t ->
            (* Compiler_utils.info "declaring alias type %s" (shortname t_name); *)
            (Type_alias t, rem, acc)
        | Tstruct _ ->
            failwith (asprintf "Unexpected struct type `%s' in module interface"
                        (shortname t_name))
        | Tabstract -> assert false
      in
      rem, (Ptype { t_name; t_desc; t_loc = Location.no_location } :: types,
            typ_symbs)
  in
  Modules.open_module modul_name;
  decl_types Modules.g_env.Modules.types ([], no_typ_symbs)

(* --- *)

let decl_var' gd v id t =
  let vd = {
    v_ident = id;
    v_type = t;
    v_linearity = Linearity.Ltop;
    v_clock = Clocks.Cbase;
    v_last = Var;
    v_loc = Location.no_location;
  } in
  gd.env <- Env.add id vd gd.env;
  gd.var_names <- SMap.add v id gd.var_names;
  vd

let decl_ident gd id t =
  let v = mk_symb (name id) in
  decl_var' gd v id t

let decl_symb_acc gd v t acc =
  let ident = ident_of_name (Symb.to_string v) in
  let vd = decl_var' gd v ident (translate_typ gd v t) in
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
  let locals = SMap.fold (decl_symb_acc gd) fni_local_vars [] in
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
  let i = List.fold_left (fun acc (v, t) -> decl_symb_acc gd v t acc) [] i in
  let o = List.sort (fun (a, _) (b, _) -> scmp b a) o in                 (* rev. *)
  let o = List.fold_left (fun acc (v, t) -> decl_symb_acc gd v t acc) [] o in
  i, o

(* --- *)

(* XXX /!\ Inputs omitted in the signature w.r.t the Controllable-Nbac model
   should not appear anywhere in equations... *)
let io_of_func_match gd { node_inputs; node_outputs } =
  let decl_arg = function
    | { a_name = Some n; a_type = ty } -> decl_ident gd (ident_of_name n) ty
    | _ -> failwith "Missing argument names in signature"
  in
  let i = List.map decl_arg node_inputs in
  let o = List.map decl_arg node_outputs in
  i, o

(* --- *)

let node_of_func gd ?node_sig n_name func =
  enter_node n_name;                                                   (* ??? *)
  let fi = gather_func_info func in
  let n_input, n_output = match node_sig with
    | None -> io_of_func gd fi
    | Some s -> io_of_func_match gd s
  in
  let block = block_of_func gd fi in
  Pnode {
    n_name;
    n_stateful = false;
    n_unsafe = false;
    n_input;
    n_output;
    n_contract = None;                                    (* <- TODO: assume? *)
    n_block = block;
    n_loc = Location.no_location;
    n_params = [];
    n_param_constraints = [];
  }

(* --- *)

let gen_func ?typ_symbs ?node_sig ~node_name func =
  let { fn_typs; fn_decls } = func_desc func in
  let fn_decls = (fn_decls :> ('f, 'f var_spec) decls) in
  let typs, typ_symbs = match typ_symbs with
    | None -> decl_typs node_name fn_typs
    | Some typ_symbs -> [], typ_symbs
  in
  let gd = mk_gen_data node_name typ_symbs fn_decls fn_typs in
  let node = node_of_func gd ?node_sig node_name func in
  node :: typs

(* --- *)

let create_prog ?(open_modul = []) modul =
  {
    p_modname = modul;
    p_opened = open_modul;
    p_desc = [];
  }

let add_to_prog e ({ p_desc } as p) =
  (* TODO: check typ duplicates *)
  { p with p_desc = List.rev (e :: List.rev p_desc); }

(* --- *)
