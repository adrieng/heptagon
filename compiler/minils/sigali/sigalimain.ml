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

(* Translation from the source language to Sigali polynomial systems *)

(* $Id: dynamic_system.ml 2652 2011-03-11 16:26:17Z delaval $ *)

open Compiler_utils
open Names
open Idents
open Types
open Clocks
open Sigali
open Location

type mtype = Tint | Tbool | Tother

exception Untranslatable

let untranslatable_warn e =
  let warn msg = warn ~cond:(!Compiler_options.warn_untranslatable) msg in
  if e.Minils.e_loc <> no_location
  then warn "abstracted expression:@.%a" print_location e.Minils.e_loc
  else warn "abstracted expression: @[<hov 2>%a@]@." Mls_printer.print_exp e

let actual_ty ty =
  match (Modules.unalias_type ty) with
  | Tid({ qual = Pervasives; name = "bool"}) -> Tbool
  | Tid({ qual = Pervasives; name = "int"}) -> Tint
  | _ -> Tother

let current_inputs : IdentSet.t ref = ref IdentSet.empty
let current_locals : IdentSet.t ref = ref IdentSet.empty

let translate_static_exp se =
  match (Static.simplify QualEnv.empty se).se_desc with
  | Sint(v) -> Cint(v)
  | Sfloat(_) -> raise Untranslatable
  | Sbool(true)
  | Sconstructor { qual = Pervasives; name = "true" }
    -> Ctrue
  | Sbool(false)
  | Sconstructor { qual = Pervasives; name = "false" }
    -> Cfalse
  | Sop({ qual = Pervasives; name = "~-" },[{se_desc = Sint(v)}]) ->
      Cint(-v)
  | _ -> raise Untranslatable


let rec translate_pat = function
  | Minils.Evarpat(x) -> [x]
  | Minils.Etuplepat(pat_list) ->
      List.fold_right (fun pat acc -> (translate_pat pat) @ acc) pat_list []

let rec translate_ck pref e = function
  | Cbase | Cvar { contents = Cindex _ } ->
      e
  | Cvar { contents = Clink ck } -> translate_ck pref e ck
  | Con(ck,c,var) ->
      let e = translate_ck pref e ck in
      Swhen(e,
            match (shortname c) with
              "true" -> Sigali.Svar(pref ^ (name var))
            | "false" -> Snot(Sigali.Svar(pref ^ (name var)))
            | _ -> assert false)


let rec translate_ext prefix ({ Minils.w_desc = desc; Minils.w_ty = ty }) =
  match desc with
  | Minils.Wconst(v) ->
      begin match (actual_ty ty) with
      | Tbool -> Sconst(translate_static_exp v)
      | Tint -> a_const (Sconst(translate_static_exp v))
      | Tother -> raise Untranslatable
      end
  | Minils.Wvar(n) ->
      (* get variable iff it is Boolean or local *)
      begin match (actual_ty ty) with
      | Tbool ->
          Sigali.Svar(prefix ^ (name n))
      | Tint when (IdentSet.mem n !current_locals) ->
          Sigali.Svar(prefix ^ (name n))
      | _ ->
          raise Untranslatable
      end
  (* TODO remove if this works without *)
  (* | Minils.Wwhen(e, c, var) when ((actual_ty e.Minils.w_ty) = Tbool) -> *)
  (*     let e = translate_ext prefix e in *)
  (*     Swhen(e, *)
  (*           match (shortname c) with *)
  (*             "true" -> Svar(prefix ^ (name var)) *)
  (*           | "false" -> Snot(Svar(prefix ^ (name var))) *)
  (*           | _ -> assert false) *)
  | Minils.Wwhen(e, _c, _var) ->
      translate_ext prefix e
  | Minils.Wfield(_) ->
      raise Untranslatable
  | Minils.Wreinit _ -> raise Untranslatable

(* [translate e = c] *)
let rec translate prefix ({ Minils.e_desc = desc } as e) =
  match desc with
  | Minils.Eextvalue(ext) -> translate_ext prefix ext
  | Minils.Eapp (* pervasives binary or unary stateless operations *)
      ({ Minils.a_op = Minils.Efun({qual=Pervasives;name=n})},
       e_list, _) ->
      begin
        match n, e_list with
        | "not", [e] -> Snot(translate_ext prefix e)
        | "or", [e1;e2] -> Sor((translate_ext prefix e1),
                               (translate_ext prefix e2))
        | "=>", [e1;e2] -> Sor(Snot (translate_ext prefix e1),
                              (translate_ext prefix e2))
        | "&", [e1;e2] -> Sand((translate_ext prefix e1),
                               (translate_ext prefix e2))
        | "=", [e1;e2] when (actual_ty e1.Minils.w_ty) = Tbool ->
            let e1 = translate_ext prefix e1 in
            let e2 = translate_ext prefix e2 in
            (* e1 = e2 iff (e1 and e2) or (not e1 and not e2) *)
            (e1 &~ e2) |~ ((~~ e1) &~ (~~ e2))
        | "<>", [e1;e2] when (actual_ty e1.Minils.w_ty) = Tbool ->
            let e1 = translate_ext prefix e1 in
            let e2 = translate_ext prefix e2 in
            (* e1 <> e2 iff (e1 and not e2) or (not e1 and e2) *)
            (e1 &~ (~~ e2)) |~ ((~~ e1) &~ e2)
        | ("<="|"<"|">="|">"|"="), [e1;e2] ->
            let op,modv =
              begin match n with
              | "<=" -> a_inf,0
              | "<"  -> a_inf,-1
              | ">=" -> a_sup,0
              | ">"  -> a_sup,1
              | _    -> a_iminv,0  (* p(x)=k <> p = inverse image of k *)
              end in
            let e1 = translate_ext prefix e1 in
            let sig_e =
              begin match e2.Minils.w_desc with
              | Minils.Wconst({se_desc = Sint(v)}) ->
                  op e1 (Sconst(Cint(v+modv)))
              | _ ->
                  let e2 = translate_ext prefix e2 in
                  op (Splus(e1,(Sprod(e2,(Sconst(Cint(-1))))))) (Sconst(Cint(modv)))
              end in
            (* a_inf, a_sup and a_iminv : +1 to translate ideals to boolean
               polynomials *)
            Splus(sig_e,Sconst(Ctrue))
        | "<>", [e1;e2] ->
            (* e1 <> e2 --> not(a_iminv((e1+(e2*(-1))),0)) *)
            let e1 = translate_ext prefix e1 in
            let sig_e =
              begin match e2.Minils.w_desc with
              | Minils.Wconst({se_desc = Sint(v)}) ->
                  a_iminv e1 (Sconst(Cint(v)))
              | _ ->
                  let e2 = translate_ext prefix e2 in
                  a_iminv (Splus(e1,(Sprod(e2,(Sconst(Cint(-1))))))) (Sconst(Cint(0)))
              end in
            (* a_iminv : +1 to translate ideals to boolean polynomials *)
            Snot(Splus(sig_e,Sconst(Ctrue)))
        | "+", [e1;e2] -> Splus((translate_ext prefix e1),
                                (translate_ext prefix e2))
        | "-", [e1;e2] -> Splus((translate_ext prefix e1),
                                (Sprod((translate_ext prefix e2),(Sconst(Cint(-1))))))
        | "*", [e1;e2] -> Sprod((translate_ext prefix e1),
                                (translate_ext prefix e2))
        | _ -> raise Untranslatable
      end
        (* | Minils.Ewhen(e, c, var) when ((actual_ty e.Minils.e_ty) = Tbool) -> *)
        (*     let e = translate prefix e in *)
        (*     Swhen(e, *)
        (*           match (shortname c) with *)
        (*             "true" -> Svar(prefix ^ (name var)) *)
        (*           | "false" -> Snot(Svar(prefix ^ (name var))) *)
        (*           | _ -> assert false) *)
  | Minils.Ewhen(e, _c, _var) ->
      translate prefix e
  | Minils.Emerge(ck,[(c1,e1);(_c2,e2)]) ->
      let e1 = translate_ext prefix e1 in
      let e2 = translate_ext prefix e2 in
      let e1,e2 =
        begin
          match (shortname c1) with
            "true" -> e1,e2
          | "false" -> e2,e1
          | _ -> assert false
        end in
      let var_ck = Sigali.Svar(prefix ^ (name ck)) in
      begin match (actual_ty e.Minils.e_ty) with
      | Tbool -> Sdefault(Swhen(e1,var_ck),e2)
      | Tint -> a_part var_ck (a_const (Sconst(Cint(0)))) e1 e2
      | Tother -> assert false
      end
  | Minils.Eapp({Minils.a_op = Minils.Eifthenelse},[e1;e2;e3],_) ->
      let e1 = translate_ext prefix e1 in
      let e2 = translate_ext prefix e2 in
      let e3 = translate_ext prefix e3 in
      begin match (actual_ty e.Minils.e_ty) with
      | Tbool -> Sdefault(Swhen(e2,e1),e3)
      | Tint -> a_part e1 (a_const (Sconst(Cint(0)))) e2 e3
      | Tother -> assert false
      end
  | Minils.Estruct(_)
  | Minils.Eiterator(_,_,_,_,_,_) ->
      raise Untranslatable
  | Minils.Eapp({Minils.a_op = Minils.Enode(_)},_,_) ->
      failwith("Sigali: node in expressions; programs should be normalized")
  | Minils.Efby(_,_) ->
      failwith("Sigali: fby in expressions; programs should be normalized")
  | Minils.Eapp(_,_,_) ->
      raise Untranslatable
  | Minils.Emerge(_, _) -> assert false

let translate_eq f
    (acc_states,acc_init,acc_inputs,acc_eqs)
    { Minils.eq_lhs = pat; Minils.eq_rhs = e; eq_base_ck = ck } =

  let prefix = f ^ "_" in

  let prefixed n = prefix ^ n in

  let { Minils.e_desc = desc } = e in
  match pat, desc with
  | Minils.Evarpat(n), Minils.Efby(opt_c, e') ->
      begin match (actual_ty e.Minils.e_ty) with
      | Tbool ->
          begin try
            let sn = prefixed (name n) in
            let acc_eqs,acc_init =
              match opt_c with
              | None -> acc_eqs,Cfalse::acc_init
              | Some(c) ->
                  let c = translate_static_exp c in
                  (extend
                     initialisations
                     (Slist[Sequal(Sigali.Svar(sn),Sconst(c))]))::acc_eqs,
                  c::acc_init
            in
            let e_next = translate_ext prefix e' in
            let e_next = translate_ck prefix e_next ck in
            current_locals := IdentSet.add n !current_locals;
            (n,sn)::acc_states,
            acc_init,acc_inputs,
            (extend
               evolutions
               (Slist[Sdefault(e_next,Sigali.Svar(sn))]))
            ::acc_eqs
          with Untranslatable ->
            untranslatable_warn e;
            (* e is abstracted ; n is Boolean and can be added as
               uncontrollable input *)
            current_inputs := IdentSet.add n !current_inputs;
            acc_states,acc_init,
            (acc_inputs @ [(n,(prefixed (name n)))]),
            acc_eqs
          end
      | _ ->
          untranslatable_warn e;
          (* Mark n as input: unusable as local variable *)
          warn ~cond:(!Compiler_options.warn_abstractions)
            "Adding non-bool variable %s in current_inputs@\n" (name n);
          current_inputs := IdentSet.add n !current_inputs;
          acc_states,acc_init,acc_inputs,acc_eqs
      end
  | pat, Minils.Eapp({ Minils.a_op = (Minils.Enode f|Minils.Efun f); },
                     _e_list, None) when f.qual <> Pervasives ->
      (*
        (y1,...,yp) = f(x1,...,xn)

        add inputs y1,...,yp. Link between yi and f's contract has
        been done in the pass "Contracts".
      *)
      let ident_list = translate_pat pat in
      let acc_inputs =
        acc_inputs @
          (List.map
             (fun id ->
                current_inputs := IdentSet.add id !current_inputs;
                (id,(prefixed (name id))))
             ident_list) in
      acc_states,acc_init,
      acc_inputs,acc_eqs
  | Minils.Evarpat(n), _ ->
      begin try
        (* assert : no fby, no node application in e *)
        let e' = translate prefix e in
        (* let e' = *)
        (*   begin match (actual_ty e.Minils.e_ty) with *)
        (*   | Tbool -> translate_ck prefix e' ck *)
        (*   | _ -> e' *)
        (*   end in *)
        current_locals := IdentSet.add n !current_locals;
        acc_states,acc_init,
        acc_inputs,
        { stmt_name = prefixed (name n);
          stmt_def  = e' }::acc_eqs
        with Untranslatable ->
          untranslatable_warn e;
          current_inputs := IdentSet.add n !current_inputs;
          let acc_inputs =
            match actual_ty e.Minils.e_ty with
              | Tbool -> acc_inputs @ [(n,(prefixed (name n)))]
              | _ -> acc_inputs
          in
          acc_states,acc_init,acc_inputs,acc_eqs
      end
  | _ -> assert false

let translate_eq_list f eq_list =
  List.fold_left
    (fun (acc_states,acc_init, acc_inputs,acc_eqs) eq ->
       translate_eq f (acc_states,acc_init,acc_inputs,acc_eqs) eq)
    ([],[],[],[])
    eq_list

let translate_contract f contract =
  let prefix = f ^ "_" in
  let var_a = prefix ^ "assume" in
  let var_g = prefix ^ "guarantee" in
  match contract with
  | None ->
      let body =
        [{ stmt_name = var_g; stmt_def = Sconst(Ctrue) };
         { stmt_name = var_a; stmt_def = Sconst(Ctrue) }] in
      [],[],[],body,(Sigali.Svar(var_a),Sigali.Svar(var_g)),[],[],[],[]
  | Some {Minils.c_local = locals;
          Minils.c_eq = l_eqs;
          Minils.c_assume = e_a;
          Minils.c_objectives = objs;
          Minils.c_assume_loc = e_a_loc;
          Minils.c_enforce_loc = e_g_loc;
          Minils.c_controllables = cl} ->
      let states,init,inputs,body = translate_eq_list f l_eqs in
      let e_a = translate_ext prefix e_a in
      let e_a_loc = translate_ext prefix e_a_loc in
      let e_g_loc = translate_ext prefix e_g_loc in

      (* separate reachability and attractivity and build one security objective [e_g] *)
      let e_g,sig_objs =
        List.fold_left
          (fun (e_g,sig_objs) o ->
             let e_obj = translate_ext prefix o.Minils.o_exp in
             match o.Minils.o_kind with
             | Minils.Obj_enforce -> (e_g &~ e_obj), sig_objs
             | Minils.Obj_reachable -> e_g, (Reachability e_obj) :: sig_objs
             | Minils.Obj_attractive -> e_g, (Attractivity e_obj) :: sig_objs)
          (e_g_loc,[])
          objs in
      let sig_objs = List.rev sig_objs in

      let body =
        {stmt_name = var_g; stmt_def = e_g } ::
        {stmt_name = var_a; stmt_def = e_a &~ e_a_loc } ::
        body in
      let controllables =
        List.map
          (fun ({ Minils.v_ident = id } as v) -> v,(prefix ^ (name id))) cl in
      states,init,inputs,body,(Sigali.Svar(var_a),Sigali.Svar(var_g)),
      controllables,(locals@cl),l_eqs,sig_objs



let translate_node
    ({ Minils.n_name = {name = f};
       Minils.n_input = i_list; Minils.n_output = o_list;
       Minils.n_local = _d_list; Minils.n_equs = eq_list;
       Minils.n_contract = contract } as node) =
  current_inputs :=
    List.fold_left
      (fun set v_d -> IdentSet.add v_d.Minils.v_ident set)
      IdentSet.empty
      i_list;
  current_locals := IdentSet.empty;
  (* keep only Boolean inputs *)
  let i_list =
    List.filter
      (fun { Minils.v_type = ty } -> (actual_ty ty) = Tbool) i_list in
  (* every variable is prefixed by its node name *)
  let inputs =
    List.map
      (fun { Minils.v_ident = v } -> v,(f ^ "_" ^ (name v))) i_list in
  let sig_outputs =
    List.map
      (fun { Minils.v_ident = v } -> f ^ "_" ^ (name v)) o_list in
  let states,init,add_inputs,body =
    translate_eq_list f eq_list in
  let states_c,init_c,inputs_c,body_c,(a_c,g_c),controllables,locals_c,eqs_c,objs =
    translate_contract f contract in
  let inputs = inputs @ add_inputs @ inputs_c in
  let body = List.rev body in
  let states = List.rev states in
  let body_c = List.rev body_c in
  let states_c = List.rev states_c in
  let mls_inputs,sig_inputs = List.split inputs in
  let mls_states,sig_states = List.split (states@states_c) in
  let mls_ctrl,sig_ctrl = List.split controllables in
  let constraints =
    List.map
      (fun v -> Sequal(Ssquare(Sigali.Svar(v)),Sconst(Ctrue)))
      (sig_inputs@sig_ctrl) in
  let constraints = constraints @ [Sequal (a_c,Sconst(Ctrue))] in
  let body_sink, sig_states_full, obj_exp =
    if !Compiler_options.nosink then
      ([], sig_states, g_c)
    else
      begin
        (* Sink state when the guarantee part of the contract becomes false *)
        (* f_error_state state variable initialized to true; become false
           the instant after the guarantee part is false *)
        let error_state_name = f ^ "_error_state" in
        let sig_states_full = sig_states @ [error_state_name] in
        let body_sink =
          [(extend
              initialisations
              (Slist[Sequal(Sigali.Svar(error_state_name),Sconst(Ctrue))]));
           (extend
              evolutions
              (Slist[g_c]))] in
        (body_sink, sig_states_full, Sigali.Svar(error_state_name))
      end in
  let objs = Security(obj_exp) :: objs in
  let p = { proc_dep = [];
            proc_name = f;
            proc_inputs = sig_inputs@sig_ctrl;
            proc_uncont_inputs = sig_inputs;
            proc_outputs = sig_outputs;
            proc_controllables = sig_ctrl;
            proc_states = sig_states_full;
            proc_init = init@init_c;
            proc_constraints = constraints;
            proc_body = body@body_c@body_sink;
            proc_objectives = objs } in
  if !Compiler_options.nbvars then
    begin
      (* Print out nb of vars *)
      let nbs = List.length p.proc_states in
      let nbi = List.length inputs in
      let nbc = List.length controllables in
      Printf.printf "%s %d %d %d %d\n" f nbs nbi nbc (nbs+nbi+nbc);
    end;

  let ctrlr_call =
    begin
      match controllables with
        [] -> [] (* no controllable => no controller call *)
      | _ :: _ ->
          let ctrlr_pat = Minils.Etuplepat(List.map (fun { Minils.v_ident = v } ->
                                                       Minils.Evarpat(v))
                                             mls_ctrl) in
          let ctrlr_name = f ^ "_controller" in
          let ctrlr_fun_name = { qual = Module (String.capitalize_ascii ctrlr_name);
                                 name = ctrlr_name } in
          let ctrlr_exp =
            Minils.mk_exp
              Cbase
              (Tprod (List.map (fun _ -> Initial.tbool) mls_ctrl))
              ~linearity:Linearity.Ltop
              (Minils.Eapp(Minils.mk_app (Minils.Efun ctrlr_fun_name),
                           (List.map
                              (fun v ->
                                 Minils.mk_extvalue
                                   ~ty:Initial.tbool
                                   ~linearity:Linearity.Ltop
                                   ~clock:Cbase
                                   (Minils.Wvar v))
                              (mls_inputs@mls_states))
                           @ (List.map
                                (fun _ ->
                                   Minils.mk_extvalue
                                     ~ty:Initial.tbool
                                     ~linearity:Linearity.Ltop
                                     ~clock:Cbase
                                     (Minils.Wconst(Initial.mk_static_bool true)))
                                mls_ctrl),
                           None))
          in
          let ctrlr_call =
            Minils.mk_equation ~base_ck:Cbase false ctrlr_pat ctrlr_exp in

          let ctrlr_inputs =
            (List.map
               (fun v ->
                  Signature.mk_arg (Some v) Initial.tbool Linearity.Ltop Signature.Cbase)
               (sig_inputs@sig_states))
            @ (List.map
                 (fun v ->
                    Signature.mk_arg
                      (Some ("p_" ^ v)) Initial.tbool Linearity.Ltop Signature.Cbase)
                 sig_ctrl) in
          let ctrlr_outputs =
            List.map
              (fun v ->
                 Signature.mk_arg (Some v) Initial.tbool Linearity.Ltop Signature.Cbase)
              sig_ctrl in
          let ctrlr_signature =
            Signature.mk_node Location.no_location ~extern:false
              ctrlr_inputs ctrlr_outputs false false [] in
          (* Add controller into modules *)
          Modules.add_value ctrlr_fun_name ctrlr_signature;
          [ctrlr_call]
    end in

  let node =
    { node with
        Minils.n_contract = None;
        Minils.n_local = node.Minils.n_local @ locals_c;
        Minils.n_equs = ctrlr_call @ (node.Minils.n_equs @ eqs_c);
    } in
  node, p

let program p =
  let acc_proc, acc_p_desc =
    List.fold_left
      (fun (acc_proc,acc_p_desc) -> function
        | Minils.Pnode(node) as p when node.Minils.n_contract = None ->
            (acc_proc,p::acc_p_desc)
        | Minils.Pnode(node) as p when node.Minils.n_params <> [] ->
            warn ~cond:(!Compiler_options.warn_untranslatable)
              "Unsupported@ translation@ of@ parametric@ node@ `%s'@ with@ \
               contract@ into@ Z/3Z!" (Names.fullname node.Minils.n_name);
            (acc_proc,p::acc_p_desc)
        | Minils.Pnode(node) ->
            let (node,proc) = translate_node node in
            (proc::acc_proc),((Minils.Pnode(node))::acc_p_desc)
        | p -> (acc_proc,p::acc_p_desc))
      ([],[])
      p.Minils.p_desc in
  let procs = List.rev acc_proc in
  let filename = filename_of_name (modul_to_string p.Minils.p_modname) in
  let dirname = build_path (filename ^ "_z3z") in
  let dir = clean_dir dirname in
  Sigali.Printer.print dir procs;
  { p with Minils.p_desc = List.rev acc_p_desc }
