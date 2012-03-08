(****************************************************)
(*                                                  *)
(*  Heptagon/BZR                                    *)
(*                                                  *)
(*  Author : Gwenaël Delaval                        *)
(*  Organization : UJF, LIG                         *)
(*                                                  *)
(****************************************************)

(* Translation from the source language to Sigali polynomial systems *)

(* $Id: dynamic_system.ml 2652 2011-03-11 16:26:17Z delaval $ *)

open Misc
open Compiler_utils
open Names
open Name_utils
open Idents
open Signature
open Clocks
open Sigali

type mtype = Tint | Tbool | Tother

let actual_ty = function
  | Tid({ qual = Pervasives; name = "bool"}) -> Tbool
  | Tid({ qual = Pervasives; name = "int"}) -> Tint
  | _ -> Tother

let var_list prefix n =
  let rec varl acc = function
    | 0 -> acc
    | n ->
        let acc = (prefix ^ (string_of_int n)) :: acc in
        varl acc (n-1) in
  varl [] n

let dummy_prefix = "d"

let translate_static_exp se =
  match se.se_desc with
  | Sint(v) -> Cint (Int32.to_int v) (* TODO: use Int32s in Sigali?! *)
  | Sfloat(_) -> failwith("Sigali: floats not implemented")
  | Sbool(true) -> Ctrue
  | Sbool(false) -> Cfalse
  | Sop({ qual = Pervasives; name = "~-" },[{se_desc = Sint(v)}]) ->
      Cint(- (Int32.to_int v))
  | _ ->
      Format.printf "Constant %a@\n"
        Global_printer.print_static_exp se;
      failwith("Sigali: untranslatable constant")


let rec translate_pat = function
  | Minils.Evarpat(x) -> [name x]
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
              "true" -> Svar(pref ^ (name var))
            | "false" -> Snot(Svar(pref ^ (name var)))
            | _ -> assert false)


let rec translate_ext prefix ({ Minils.w_desc = desc; Minils.w_ty = ty } as e) =
  match desc with
    | Minils.Wconst(v) ->
        begin match (actual_ty ty) with
        | Tbool -> Sconst(translate_static_exp v)
        | Tint -> a_const (Sconst(translate_static_exp v))
        | Tother -> failwith("Sigali: untranslatable type")
        end
    | Minils.Wvar(n) -> Svar(prefix ^ (name n))
    | Minils.Wwhen(e, c, var) when ((actual_ty e.Minils.w_ty) = Tbool) ->
        let e = translate_ext prefix e in
        Swhen(e,
              match (shortname c) with
                "true" -> Svar(prefix ^ (name var))
              | "false" -> Snot(Svar(prefix ^ (name var)))
              | _ -> assert false)
    | Minils.Wwhen(e, _c, _var) ->
        translate_ext prefix e
    | Minils.Wfield(_) ->
        failwith("Sigali: structures not implemented")
    | Minils.Wreinit _ -> failwith("Sigali: reinit not implemented")

(* [translate e = c] *)
let rec translate prefix ({ Minils.e_desc = desc; Minils.e_ty = ty } as e) =
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
          | "&", [e1;e2] -> Sand((translate_ext prefix e1),
                                 (translate_ext prefix e2))
          | ("<="|"<"|">="|">"), [e1;e2] ->
              let op,modv =
                begin match n with
                | "<=" -> a_inf,0
                | "<"  -> a_inf,-1
                | ">=" -> a_sup,0
                | _    -> a_sup,1
                end in
              let e1 = translate_ext prefix e1 in
              let sig_e =
                begin match e2.Minils.w_desc with
                | Minils.Wconst({se_desc = Sint(v)}) ->
                    op e1 (Sconst(Cint(Int32.to_int v + modv)))
                | _ ->
                    let e2 = translate_ext prefix e2 in
                    op (Sminus(e1,e2)) (Sconst(Cint(modv)))
                end in
              (* a_inf and a_sup : +1 to translate ideals to boolean
                 polynomials *)
              Splus(sig_e,Sconst(Ctrue))
          | "+", [e1;e2] -> Splus((translate_ext prefix e1),
                                  (translate_ext prefix e2))
          | "-", [e1;e2] -> Sminus((translate_ext prefix e1),
                                   (translate_ext prefix e2))
          | "*", [e1;e2] -> Sprod((translate_ext prefix e1),
                                  (translate_ext prefix e2))
          | ("="
            | "<>"),_ -> failwith("Sigali: '=' or '<>' not yet implemented")
          | _ -> assert false
        end
    | Minils.Ewhen(e, c, var) when ((actual_ty e.Minils.e_ty) = Tbool) ->
        let e = translate prefix e in
        Swhen(e,
              match (shortname c) with
                "true" -> Svar(prefix ^ (name var))
              | "false" -> Snot(Svar(prefix ^ (name var)))
              | _ -> assert false)
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
        let var_ck = Svar(prefix ^ (name ck)) in
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
    | Minils.Estruct(_) ->
        failwith("Sigali: structures not implemented")
    | Minils.Eiterator(_,_,_,_,_,_) ->
        failwith("Sigali: iterators not implemented")
    | Minils.Eapp({Minils.a_op = Minils.Enode(_)},_,_) ->
        failwith("Sigali: node in expressions; programs should be normalized")
    | Minils.Efby(_,_) ->
        failwith("Sigali: fby in expressions; programs should be normalized")
    | Minils.Eapp(_,_,_) ->
        Format.printf "Application : %a@\n"
          Mls_printer.print_exp e;
        failwith("Sigali: not supported application")
    | Minils.Emerge(_, _) -> assert false

let rec translate_eq env f
    (acc_dep,acc_states,acc_init,acc_inputs,acc_ctrl,acc_cont,acc_eqs)
    { Minils.eq_lhs = pat; Minils.eq_rhs = e; eq_base_ck = ck } =

  let prefix = f ^ "_" in

  let prefixed n = prefix ^ n in

  let { Minils.e_desc = desc } = e in
  match pat, desc with
  | Minils.Evarpat(n), Minils.Efby(opt_c, e) ->
      let sn = prefixed (name n) in
      let sm = prefix ^ "mem_" ^ (name n) in
(*       let acc_eqs = *)
(*         (extend *)
(*            constraints *)
(*            (Slist[Sequal(Ssquare(Svar(sn)),Sconst(Ctrue))]))::acc_eqs in *)
      let acc_eqs,acc_init =
        match opt_c with
        | None -> acc_eqs,Cfalse::acc_init
        | Some(c) ->
            let c = translate_static_exp c in
            (extend
               initialisations
               (Slist[Sequal(Svar(sn),Sconst(c))]))::acc_eqs,
            c::acc_init
      in
      let e_next = translate_ext prefix e in
      let e_next = translate_ck prefix e_next ck in
      acc_dep,
      sn::acc_states,
      acc_init,acc_inputs,acc_ctrl,acc_cont,
      (extend
         evolutions
         (Slist[Sdefault(e_next,Svar(sn))]))
        (* TODO *)
(*       ::{ stmt_name = sn; *)
(*           stmt_def  = translate_ck prefix (Svar(sm)) ck } *)
      ::acc_eqs
  | pat, Minils.Eapp({ Minils.a_op = Minils.Enode g_name;
                       Minils.a_id = Some a_id;
                       Minils.a_inlined = inlined }, e_list, None) ->
      (*
        g : n states (gq1,...,gqn), p inputs (gi1,...,gip), m outputs (go1,...,gom)

        case inlined :
          var_g : [gq1,...,gqn,gi1,...,gip]
          var_inst_g : [hq1,...,hqn,e1,...,en]
        case non inlined :
          add inputs go1',...,gom'
          var_g : [gq1,...,gqn,gi1,...,gip,go1,...,gom]
          var_inst_g : [hq1,...,hqn,e1,...,en,go1',...,gom']

        declare(d1,...,dn)

        d : [d1,...,dn]
        % q1 = if ck then d1 else hq1 %
        q1 : d1 when ck default hq1
        ...
        qn : dn when ck default hqn

        % P_inst = P[var_inst_g/var_g] %
        evol_g : l_subst(evolution(g),var_g,var_inst_g);
        evolutions : concat(evolutions,l_subst([q1,...,qn],[d1,...,dn],evol_g)
        initialisations : concat(initialisations, [subst(initial(g),var_g,var_inst_g)])
        constraints : concat(constraints, [subst(constraint(g),var_g,var_inst_g)])

        case inlined :
          ho1 : subst(go1,var_g,var_inst_g)
          ...
          hom : subst(gom,var_g,var_inst_g)
        case non inlined :
          (nothing)
      *)
      let g_name = shortname g_name in
      let (g_p,g_p_contract) = NamesEnv.find g_name env in
      let g = if inlined then g_name else g_name ^ "_contract" in
      (* add dependency *)
      let acc_dep = g :: acc_dep in
      let name_list = translate_pat pat in
      let g_p = if inlined then g_p else g_p_contract in
      (* var_g : [gq1,...,gqn,gi1,...,gip] *)
      let var_g = "var_" ^ g in
      let vars =
        match inlined with
        | true -> g_p.proc_states @ g_p.proc_inputs
        | false -> g_p.proc_states @ g_p.proc_inputs @ g_p.proc_outputs in
      let acc_eqs =
        { stmt_name = var_g;
          stmt_def = Slist(List.map (fun v -> Svar(v)) vars) }::acc_eqs in
      (* var_inst_g : [hq1,...,hqn,e1,...,en] *)
      let var_inst_g = "var_inst_" ^ g in
      (* Coding contract states : S_n_id_s *)
      (* id being the id of the application *)
      (* n being the length of id *)
      (* s being the name of the state*)
      let a_id = (name a_id) in
      let id_length = String.length a_id in
      let s_prefix = "S_" ^ (string_of_int id_length) ^ "_" ^ a_id ^ "_" in
      let new_states_list =
        List.map
          (fun g_state ->
             (* Remove "g_" prefix *)
             let l = String.length g in
             let s =
               String.sub
                 g_state (l+1)
                 ((String.length g_state)-(l+1)) in
             prefixed (s_prefix ^ s))
          g_p.proc_states in
      let e_states = List.map (fun hq -> Svar(hq)) new_states_list in
      let e_list = List.map (translate_ext prefix) e_list in
      let e_outputs,acc_inputs =
        match inlined with
        | true -> [],acc_inputs
        | false ->
            let new_outputs =
              List.map (fun name -> prefixed name) name_list in
            (List.map (fun v -> Svar(v)) new_outputs),(acc_inputs@new_outputs) in
      let vars_inst = e_states@e_list@e_outputs in
      let acc_eqs =
        { stmt_name = var_inst_g;
          stmt_def = Slist(vars_inst); }::acc_eqs in
      let acc_states = List.rev_append new_states_list acc_states in
      let acc_init = List.rev_append g_p.proc_init acc_init in
      (* declare(d1,...,dn) *)
      let dummy_list = var_list dummy_prefix (List.length g_p.proc_states) in
      (* d : [d1,...dn] *)
      let acc_eqs =
        {stmt_name = dummy_prefix;
         stmt_def = Slist(List.map (fun di -> Svar(di)) dummy_list)}::acc_eqs in
      (* qi = di when ck default hqi *)
      let q_list = List.map (fun _ -> "q_" ^ (gen_symbol ())) g_p.proc_states in
      let e_list =
        List.map2
          (fun hq d ->
             let e = Svar(d) in
             let e = translate_ck (prefixed "") e ck in
             Sdefault(e,Svar(hq)))
          new_states_list dummy_list in
      let acc_eqs =
        List.fold_left2
          (fun acc_eqs q e -> {stmt_name = q; stmt_def = e}::acc_eqs)
          acc_eqs q_list e_list in
      (* evol_g : l_subst(evolution(g),var_g,var_inst_g); *)
      let evol_g = "evol_" ^ g in
      let acc_eqs =
        {stmt_name = evol_g;
         stmt_def = l_subst (evolution (Svar g)) (Svar var_g) (Svar var_inst_g)}
        ::acc_eqs in
      (* evolutions : concat(evolutions,l_subst([q1,...,qn],[d1,...,dn],evol_g) *)
      let acc_eqs =
        (extend evolutions (l_subst
                              (Slist (List.map (fun q -> Svar(q)) q_list))
                              (Slist (List.map (fun d -> Svar(d)) dummy_list))

                              (Svar evol_g)))
        ::acc_eqs in
      (* initialisations : concat(initialisations, [subst(initial(g),var_g,var_inst_g)]) *)
      let acc_eqs =
        (extend initialisations (Slist[subst
                                         (initial (Svar g))
                                         (Svar var_g)
                                         (Svar var_inst_g)]))
        :: acc_eqs in
      (* constraints : concat(constraints, [subst(constraint(g),var_g,var_inst_g)]) *)
      let acc_eqs =
        (extend constraints (Slist[subst
                                     (pconstraint (Svar g))
                                     (Svar var_g)
                                     (Svar var_inst_g)]))
        ::acc_eqs in
      (* if inlined, hoi : subst(goi,var_g,var_inst_g) *)
      let acc_eqs =
        match inlined with
        | true ->
            List.fold_left2
              (fun acc_eqs o go ->
                 {stmt_name = prefixed o;
                  stmt_def = subst (Svar(go)) (Svar(var_g)) (Svar(var_inst_g))}
                 ::acc_eqs)
              acc_eqs name_list g_p.proc_outputs
        | false -> acc_eqs in
      (* assume & guarantee *)
      (* f_g_assume_x : subst(g_assume,var_g,var_inst_g) *)
      (* f_g_guarantee_x : subst(g_guarantee,var_g,var_inst_g) *)
      let var_assume = prefixed (g ^ "_assume_" ^ (gen_symbol ())) in
      let var_guarantee = prefixed (g ^ "_guarantee_" ^ (gen_symbol ())) in
      let acc_eqs =
        {stmt_name = var_assume;
         stmt_def = subst (Svar(g ^ "_assume")) (Svar(var_g)) (Svar(var_inst_g))} ::
          {stmt_name = var_guarantee;
           stmt_def = subst (Svar(g ^ "_guarantee")) (Svar(var_g)) (Svar(var_inst_g))} ::
          acc_eqs in
      let acc_cont =
        (Svar(var_assume),Svar(var_guarantee)) :: acc_cont in
      acc_dep,acc_states,acc_init,
      acc_inputs,acc_ctrl,acc_cont,acc_eqs
  | pat, Minils.Eapp({ Minils.a_op = Minils.Enode g_name;
                       Minils.a_id = Some a_id;
                       Minils.a_inlined = inlined }, e_list, Some r) ->
      (*
        g : n states (gq1,...,gqn), p inputs (gi1,...,gip),
        n init states (gq1_0,...,gqn_0)

        case inlined :
          var_g : [gq1,...,gqn,gi1,...,gip]
          var_inst_g : [hq1,...,hqn,e1,...,en]
        case non inlined :
          add inputs go1',...,gom'
          var_g : [gq1,...,gqn,gi1,...,gip,go1,...,gom]
          var_inst_g : [hq1,...,hqn,e1,...,en,go1',...,gom']

        declare(d1,...,dn)

        d : [d1,...,dn]
        % q1 = if ck then (if r then gq1_0 else d1) else hq1 %
        q1 : (gq1_0 when r default d1) when ck default hq1
        ...
        qn : (gqn_0 when r default dn) when ck default hqn

        % P_inst = P[var_inst_g/var_g] %
        evol_g : l_subst(evolution(g),var_g,var_inst_g);
        evolutions : concat(evolutions,l_subst([q1,...,qn],[d1,...,dn],evol_g)
        initialisations : concat(initialisations, [subst(initial(g),var_g,var_inst_g)])
        constraints : concat(constraints, [subst(constraint(g),var_g,var_inst_g)])

        case inlined :
          ho1 : subst(go1,var_g,var_inst_g)
          ...
          hom : subst(gom,var_g,var_inst_g)
        case non inlined :
          (nothing)
      *)
      let g_name = shortname g_name in
      let (g_p,g_p_contract) = NamesEnv.find g_name env in
      let g = if inlined then g_name else g_name ^ "_contract" in
      (* add dependency *)
      let acc_dep = g :: acc_dep in
      let name_list = translate_pat pat in
      let g_p = if inlined then g_p else g_p_contract in
      (* var_g : [gq1,...,gqn,gi1,...,gip] *)
      let var_g = "var_" ^ g in
      let vars =
        match inlined with
        | true -> g_p.proc_states @ g_p.proc_inputs
        | false -> g_p.proc_states @ g_p.proc_inputs @ g_p.proc_outputs in
      let acc_eqs =
        { stmt_name = var_g;
          stmt_def = Slist(List.map (fun v -> Svar(v)) vars) }::acc_eqs in
      (* var_inst_g : [hq1,...,hqn,e1,...,en] *)
      let var_inst_g = "var_inst_" ^ g in
      (* Coding contract states : S_n_id_s *)
      (* id being the id of the application *)
      (* n being the length of id *)
      (* s being the name of the state*)
      let a_id = name a_id in
      let id_length = String.length a_id in
      let s_prefix = "S_" ^ (string_of_int id_length) ^ "_" ^ a_id ^ "_" in
      let new_states_list =
        List.map
          (fun g_state ->
             (* Remove "g_" prefix *)
             let l = (String.length g) in
             let s =
               String.sub
                 g_state (l+1)
                 ((String.length g_state)-(l+1)) in
             prefixed (s_prefix ^ s))
          g_p.proc_states in
      let e_states = List.map (fun hq -> Svar(hq)) new_states_list in
      let e_list = List.map (translate_ext prefix) e_list in
      let e_outputs,acc_inputs =
        match inlined with
        | true -> [],acc_inputs
        | false ->
            let new_outputs =
              List.map (fun name -> prefixed name) name_list in
            (List.map (fun v -> Svar(v)) new_outputs),(acc_inputs@new_outputs) in
      let vars_inst = e_states@e_list@e_outputs in
      let acc_eqs =
        { stmt_name = var_inst_g;
          stmt_def = Slist(vars_inst); }::acc_eqs in
      let acc_states = List.rev_append new_states_list acc_states in
      let acc_init = List.rev_append g_p.proc_init acc_init in
      (* declare(d1,...,dn) *)
      let dummy_list = var_list dummy_prefix (List.length g_p.proc_states) in
      (* d : [d1,...dn] *)
      let acc_eqs =
        {stmt_name = dummy_prefix;
         stmt_def = Slist(List.map (fun di -> Svar(di)) dummy_list)}::acc_eqs in
      (* qi = (gqi_0 when r default di) when ck default hqi *)
      let q_list = List.map (fun _ -> "q_" ^ (gen_symbol ())) g_p.proc_states in
      let e_list =
        List.map2
          (fun (q0,hq) d ->
             let e = Sdefault(Swhen(Sconst(q0),
                                    Svar(prefixed (name r))),Svar(d)) in
             let e = translate_ck (prefixed "") e ck in
             Sdefault(e,Svar(hq)))
          (List.combine g_p.proc_init new_states_list) dummy_list in
      let acc_eqs =
        List.fold_left2
          (fun acc_eqs q e -> {stmt_name = q; stmt_def = e}::acc_eqs)
          acc_eqs q_list e_list in
      (* evol_g : l_subst(evolution(g),var_g,var_inst_g); *)
      let evol_g = "evol_" ^ g in
      let acc_eqs =
        {stmt_name = evol_g;
         stmt_def = l_subst (evolution (Svar g)) (Svar var_g) (Svar var_inst_g)}
        ::acc_eqs in
      (* evolutions : concat(evolutions,l_subst([q1,...,qn],[d1,...,dn],evol_g) *)
      let acc_eqs =
        (extend evolutions (l_subst
                              (Slist (List.map (fun q -> Svar(q)) q_list))
                              (Slist (List.map (fun d -> Svar(d)) dummy_list))

                              (Svar evol_g)))
        ::acc_eqs in
      (* initialisations : concat(initialisations, [subst(initial(g),var_g,var_inst_g)]) *)
      let acc_eqs =
        (extend initialisations (Slist[subst
                                         (initial (Svar g))
                                         (Svar var_g)
                                         (Svar var_inst_g)]))
        :: acc_eqs in
      (* constraints : concat(constraints, [subst(constraint(g),var_g,var_inst_g)]) *)
      let acc_eqs =
        (extend constraints (Slist[subst
                                     (pconstraint (Svar g))
                                     (Svar var_g)
                                     (Svar var_inst_g)]))
        ::acc_eqs in
      (* if inlined, hoi : subst(goi,var_g,var_inst_g) *)
      let acc_eqs =
        match inlined with
        | true ->
            List.fold_left2
              (fun acc_eqs o go ->
                 {stmt_name = prefixed o;
                  stmt_def = subst (Svar(go)) (Svar(var_g)) (Svar(var_inst_g))}
                 ::acc_eqs)
              acc_eqs name_list g_p.proc_outputs
        | false -> acc_eqs in
      (* assume & guarantee *)
      (* f_g_assume_x : subst(g_assume,var_g,var_inst_g) *)
      (* f_g_guarantee_x : subst(g_guarantee,var_g,var_inst_g) *)
      let var_assume = prefixed (g ^ "_assume_" ^ (gen_symbol ())) in
      let var_guarantee = prefixed (g ^ "_guarantee_" ^ (gen_symbol ())) in
      let acc_eqs =
        {stmt_name = var_assume;
         stmt_def = subst (Svar(g ^ "_assume")) (Svar(var_g)) (Svar(var_inst_g))} ::
          {stmt_name = var_guarantee;
           stmt_def = subst (Svar(g ^ "_guarantee")) (Svar(var_g)) (Svar(var_inst_g))} ::
          acc_eqs in
      let acc_cont =
        (Svar(var_assume),Svar(var_guarantee)) :: acc_cont in
      acc_dep,acc_states,acc_init,
      acc_inputs,acc_ctrl,acc_cont,acc_eqs
  | Minils.Evarpat(n), _ ->
      (* assert : no fby, no node application in e *)
      let e' = translate prefix e in
      let e' =
        begin match (actual_ty e.Minils.e_ty) with
        | Tbool -> translate_ck prefix e' ck
        | _ -> e'
        end in
      acc_dep,acc_states,acc_init,
      acc_inputs,acc_ctrl,acc_cont,
      { stmt_name = prefixed (name n);
        stmt_def  = e' }::acc_eqs
  | _ -> assert false

let translate_eq_list env f eq_list =
  List.fold_left
    (fun (acc_dep,acc_states,acc_init,
          acc_inputs,acc_ctrl,acc_cont,acc_eqs) eq ->
       translate_eq
         env f
         (acc_dep,acc_states,acc_init,
          acc_inputs,acc_ctrl,acc_cont,acc_eqs)
         eq)
    ([],[],[],[],[],[],[])
    eq_list

let translate_contract env f contract =
  let prefix = f ^ "_" in
  let var_a = prefix ^ "assume" in
  let var_g = prefix ^ "guarantee" in
  match contract with
  | None ->
      let body =
        [{ stmt_name = var_g; stmt_def = Sconst(Ctrue) };
         { stmt_name = var_a; stmt_def = Sconst(Ctrue) }] in
      [],[],[],body,(Svar(var_a),Svar(var_g)),[]
  | Some {Minils.c_local = _locals;
          Minils.c_eq = l_eqs;
          Minils.c_assume = e_a;
          Minils.c_enforce = e_g;
          Minils.c_controllables = cl} ->
      let dep,states,init,inputs,
        controllables,_contracts,body =
        translate_eq_list env f l_eqs in
      assert (inputs = []);
      assert (controllables = []);
      let e_a = translate_ext prefix e_a in
      let e_g = translate_ext prefix e_g in
      let body =
        {stmt_name = var_g; stmt_def = e_g} ::
        {stmt_name = var_a; stmt_def = e_a} ::
        body in
      let controllables =
        List.map (fun { Minils.v_ident = id } -> prefix ^ (name id)) cl in
      dep,states,init,body,(Svar(var_a),Svar(var_g)),controllables



let rec build_environment contracts =
  match contracts with
  | [] -> [],Sconst(Ctrue)
  | [a,g] -> [a =>~ g],g
  | (a,g)::l ->
      let conts,assumes = build_environment l in
      ((a =>~ g) :: conts),(g &~ assumes)

let translate_node env
    ({ Minils.n_name = {name = f};
       Minils.n_input = i_list; Minils.n_output = o_list;
       Minils.n_local = _d_list; Minils.n_equs = eq_list;
       Minils.n_contract = contract } as node) =
  (* every variable is prefixed by its node name *)
  let inputs =
    List.map
      (fun { Minils.v_ident = v } -> f ^ "_" ^ (name v)) i_list in
  let outputs =
    List.map
      (fun { Minils.v_ident = v } -> f ^ "_" ^ (name v)) o_list in
  let dep,states,init,add_inputs,add_controllables,contracts,body =
    translate_eq_list env f eq_list in
  let dep_c,states_c,init_c,body_c,(a_c,g_c),controllables =
    translate_contract env f contract in
  let inputs = inputs @ add_inputs in
  let controllables = controllables @ add_controllables in
  let body = List.rev body in
  let states = List.rev states in
  let body_c = List.rev body_c in
  let states_c = List.rev states_c in
  let constraints =
    List.map
      (fun v -> Sequal(Ssquare(Svar(v)),Sconst(Ctrue)))
      (inputs@controllables) in
  let contracts_components,assumes_components =
    build_environment contracts in
  let constraints = constraints @
    contracts_components @ [Sequal (a_c,Sconst(Ctrue))] in
  let impl = g_c &~ assumes_components in
  let obj = Security(impl) in
  let p = { proc_dep = unique (dep @ dep_c);
            proc_name = f;
            proc_inputs = inputs@controllables;
            proc_uncont_inputs = inputs;
            proc_outputs = outputs;
            proc_controllables = controllables;
            proc_states = states@states_c;
            proc_init = init@init_c;
            proc_constraints = constraints;
            proc_body = body@body_c;
            proc_objectives = [obj] } in
  (* Hack : save inputs and states names for controller call *)
  let remove_prefix =
    let n = String.length f in
    fun s ->
      String.sub s (n+1) ((String.length s) - (n+1)) in
  node.Minils.n_controller_call <-
    (List.map remove_prefix inputs,
     List.map remove_prefix (states@states_c));

  let f_contract = f ^ "_contract" in
  let inputs_c =
    List.map
      (fun { Minils.v_ident = v } -> f_contract ^ "_" ^ (name v)) i_list in
  let outputs_c =
    List.map
      (fun { Minils.v_ident = v } -> f_contract ^ "_" ^ (name v)) o_list in
  let dep_c,states_c,init_c,body_c,(_a_c,_g_c),_controllables =
    translate_contract env f_contract contract in
  let states_c = List.rev states_c in
  let body_c = List.rev body_c in
  let constraints_c =
    List.map
      (fun v -> Sequal(Ssquare(Svar(v)),Sconst(Ctrue)))
      (inputs_c@outputs_c) in
  let p_c =  { proc_dep = dep_c;
               proc_name = f ^ "_contract";
               proc_inputs = inputs_c@outputs_c;
               proc_uncont_inputs = inputs_c@outputs_c;
               proc_outputs = [];
               proc_controllables = [];
               proc_states = states_c;
               proc_init = init_c;
               proc_constraints = constraints_c;
               proc_body = body_c;
               proc_objectives = [] } in
  (NamesEnv.add f (p,p_c) env), (p,p_c)

let program p =
  let _env,acc_proc =
    List.fold_left
      (fun (env,acc) p_desc ->
         match p_desc with
         | Minils.Pnode(node) ->
             let env,(proc,contract) = translate_node env node in
             env,contract::proc::acc
         | _ -> env,acc)
      (NamesEnv.empty,[])
      p.Minils.p_desc in
  let procs = List.rev acc_proc in
  let filename = filename_of_name (modul_to_string p.Minils.p_modname) in
  let dirname = build_path (filename ^ "_z3z") in
  let dir = clean_dir dirname in
  Sigali.Printer.print dir procs

