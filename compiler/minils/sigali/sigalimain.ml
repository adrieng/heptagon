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
open Idents
open Types
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
  | Sint(v) -> Cint(v)
  | Sfloat(_) -> failwith("Sigali: floats not implemented")
  | Sbool(true)
  | Sconstructor { qual = Pervasives; name = "true" }
    -> Ctrue
  | Sbool(false)
  | Sconstructor { qual = Pervasives; name = "false" }
    -> Cfalse  
  | Sop({ qual = Pervasives; name = "~-" },[{se_desc = Sint(v)}]) ->
      Cint(-v)
  | _ ->
      Format.printf "Constant %a@\n"
        Global_printer.print_static_exp se;
      failwith("Sigali: untranslatable constant")


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
              "true" -> Svar(pref ^ (name var))
            | "false" -> Snot(Svar(pref ^ (name var)))
            | _ -> assert false)


let rec translate_ext prefix ({ Minils.w_desc = desc; Minils.w_ty = ty }) =
  match desc with
    | Minils.Wconst(v) ->
        begin match (actual_ty ty) with
        | Tbool -> Sconst(translate_static_exp v)
        | Tint -> a_const (Sconst(translate_static_exp v))
        | Tother -> failwith("Sigali: untranslatable type")
        end
    | Minils.Wvar(n) -> Svar(prefix ^ (name n))

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
        failwith("Sigali: structures not implemented")
    | Minils.Wreinit _ -> failwith("Sigali: reinit not implemented")

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
                    op e1 (Sconst(Cint(v+modv)))
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

let rec translate_eq f
    (acc_states,acc_init,acc_inputs,acc_eqs)
    { Minils.eq_lhs = pat; Minils.eq_rhs = e; eq_base_ck = ck } =

  let prefix = f ^ "_" in

  let prefixed n = prefix ^ n in

  let { Minils.e_desc = desc } = e in
  match pat, desc with
  | Minils.Evarpat(n), Minils.Efby(opt_c, e) ->
      let sn = prefixed (name n) in
      let acc_eqs =
        (extend
           constraints
           (Slist[Sequal(Ssquare(Svar(sn)),Sconst(Ctrue))]))::acc_eqs in
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
      (n,sn)::acc_states,
      acc_init,acc_inputs,
      (extend
         evolutions
         (Slist[Sdefault(e_next,Svar(sn))]))
      ::acc_eqs
  | pat, Minils.Eapp({ Minils.a_op = Minils.Enode _f; }, _e_list, None) ->
      (*
        (y1,...,yp) = f(x1,...,xn)

        add inputs y1,...,yp. Link between yi and f's contract has
        been done in the pass "Contracts".
      *)
      let ident_list = translate_pat pat in
      let acc_inputs = 
        acc_inputs @
          (List.map (fun id -> (id,(prefixed (name id)))) ident_list) in
      acc_states,acc_init,
      acc_inputs,acc_eqs
  | Minils.Evarpat(n), _ ->
      (* assert : no fby, no node application in e *)
      let e' = translate prefix e in
      (* let e' = *)
      (*   begin match (actual_ty e.Minils.e_ty) with *)
      (*   | Tbool -> translate_ck prefix e' ck *)
      (*   | _ -> e' *)
      (*   end in *)
      acc_states,acc_init,
      acc_inputs,
      { stmt_name = prefixed (name n);
        stmt_def  = e' }::acc_eqs
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
      [],[],body,(Svar(var_a),Svar(var_g)),[],[],[]
  | Some {Minils.c_local = locals;
          Minils.c_eq = l_eqs;
          Minils.c_assume = e_a;
          Minils.c_enforce = e_g;
          Minils.c_assume_loc = e_a_loc;
          Minils.c_enforce_loc = e_g_loc;
          Minils.c_controllables = cl} ->
      let states,init,inputs,body = translate_eq_list f l_eqs in
      assert (inputs = []);
      let e_a = translate_ext prefix e_a in
      let e_g = translate_ext prefix e_g in
      let e_a_loc = translate_ext prefix e_a_loc in
      let e_g_loc = translate_ext prefix e_g_loc in
      let body =
        {stmt_name = var_g; stmt_def = e_g &~ e_g_loc } ::
        {stmt_name = var_a; stmt_def = e_a &~ e_a_loc } ::
        body in
      let controllables =
        List.map
          (fun ({ Minils.v_ident = id } as v) -> v,(prefix ^ (name id))) cl in
      states,init,body,(Svar(var_a),Svar(var_g)),controllables,(locals@cl),l_eqs



let translate_node
    ({ Minils.n_name = {name = f};
       Minils.n_input = i_list; Minils.n_output = o_list;
       Minils.n_local = _d_list; Minils.n_equs = eq_list;
       Minils.n_contract = contract } as node) =
  (* every variable is prefixed by its node name *)
  let inputs =
    List.map
      (fun { Minils.v_ident = v } -> v,(f ^ "_" ^ (name v))) i_list in
  let sig_outputs =
    List.map
      (fun { Minils.v_ident = v } -> f ^ "_" ^ (name v)) o_list in
  let states,init,add_inputs,body =
    translate_eq_list f eq_list in
  let states_c,init_c,body_c,(a_c,g_c),controllables,locals_c,eqs_c =
    translate_contract f contract in
  let inputs = inputs @ add_inputs in
  let body = List.rev body in
  let states = List.rev states in
  let body_c = List.rev body_c in
  let states_c = List.rev states_c in
  let mls_inputs,sig_inputs = List.split inputs in
  let mls_states,sig_states = List.split (states@states_c) in
  let mls_ctrl,sig_ctrl = List.split controllables in
  let constraints =
    List.map
      (fun v -> Sequal(Ssquare(Svar(v)),Sconst(Ctrue)))
      (sig_inputs@sig_ctrl) in
  let constraints = constraints @ [Sequal (a_c,Sconst(Ctrue))] in
  let obj = Security(g_c) in
  let p = { proc_dep = [];
            proc_name = f;
            proc_inputs = sig_inputs@sig_ctrl;
            proc_uncont_inputs = sig_inputs;
            proc_outputs = sig_outputs;
            proc_controllables = sig_ctrl;
            proc_states = sig_states;
            proc_init = init@init_c;
            proc_constraints = constraints;
            proc_body = body@body_c;
            proc_objectives = [obj] } in

  let ctrlr_pat = Minils.Etuplepat(List.map (fun { Minils.v_ident = v } ->
                                               Minils.Evarpat(v))
                                     mls_ctrl) in
  let ctrlr_name = f ^ "_controller" in
  let ctrlr_fun_name = { qual = Module (String.capitalize ctrlr_name);
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
  
  let node =
    { node with
        Minils.n_contract = None;
        Minils.n_local = node.Minils.n_local @ locals_c;
        Minils.n_equs = ctrlr_call :: (node.Minils.n_equs @ eqs_c);
    } in
  node, p

let program p =
  let acc_proc, acc_p_desc =
    List.fold_left
      (fun (acc_proc,acc_p_desc) p_desc ->
         match p_desc with
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


