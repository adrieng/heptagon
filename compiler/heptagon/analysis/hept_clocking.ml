(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* clock checking *)

(* v_clock is expected to contain correct clocks before entering here :
     either explicit with Cbase representing the node activation clock
     or fresh_clock() for unannoted variables.
  Idem for e_ct : if explicit, it represents a clock annotation.
  Unification is done on this mutable fields.
  e_base_ck is set according to node signatures.

 *)

open Misc
open Idents
open Heptagon
open Hept_utils
open Global_printer
open Hept_printer
open Signature
open Signature
open Clocks
open Location
open Format

(** Error Kind *)
type error_kind = | Etypeclash of ct * ct | Eclockclash of ck * ck | Edefclock

let error_message loc = function
  | Etypeclash (actual_ct, expected_ct) ->
      Format.eprintf "%aClock Clash: this expression has clock %a,@\n\
                        but is expected to have clock %a.@."
        print_location loc
        print_ct actual_ct
        print_ct expected_ct;
      raise Errors.Error
  | Eclockclash (actual_ck, expected_ck) ->
      Format.eprintf "%aClock Clash: this value has clock %a,@\n\
                        but is exprected to have clock %a.@."
        print_location loc
        print_ck actual_ck
        print_ck expected_ck;
      raise Errors.Error
  | Edefclock ->
      Format.eprintf "%aArguments defining clocks should be given as names@."
        print_location loc;
      raise Errors.Error


let ck_of_name h x =
  if is_reset x
  then fresh_clock()
  else Env.find x h

let rec typing_pat h = function
  | Evarpat x -> Ck (ck_of_name h x)
  | Etuplepat pat_list -> Cprod (List.map (typing_pat h) pat_list)

let ident_list_of_pat pat =
  let rec f acc pat = match pat with
    | Evarpat id -> id::acc
    | Etuplepat pat_l -> List.fold_left f acc pat_l
  in
  List.rev (f [] pat)

(* typing the expression, returns ct, ck_base *)
let rec typing h pat e =
  let ct,base = match e.e_desc with
    | Econst _ ->
        let ck = fresh_clock() in
        Ck ck, ck
    | Evar x ->
        let ck = ck_of_name h x in
        Ck ck, ck
    | Efby (e1, e2) ->
        let ct,ck = typing h pat e1 in
        expect h pat ct e2;
        ct, ck
    | Epre(_,e) ->
        typing h pat e
    | Ewhen (e,c,n) ->
        let ck_n = ck_of_name h n in
        let base = expect h pat (skeleton ck_n e.e_ty) e in
        skeleton (Con (ck_n, c, n)) e.e_ty, Con (ck_n, c, n)
    | Emerge (x, c_e_list) ->
        let ck = ck_of_name h x in
        List.iter (fun (c,e) -> expect h pat (Ck(Con (ck,c,x))) e) c_e_list;
        Ck ck, ck
    | Estruct l ->
        let ck = fresh_clock () in
        List.iter (fun (_, e) -> expect h pat (Ck ck) e) l;
        Ck ck, ck
    | Eapp({a_op = op}, args, _) -> (* hyperchronous reset *)
        let base_ck = fresh_clock () in
        let ct = typing_app h base_ck pat op args in
        ct, base_ck
    | Eiterator (it, {a_op = op}, nl, pargs, args, _) -> (* hyperchronous reset *)
        let base_ck = fresh_clock() in
        let ct = match it with
          | Imap -> (* exactly as if clocking the node *)
              typing_app h base_ck pat op (pargs@args)
          | Imapi -> (* clocking the node with the extra i input on [ck_r] *)
              let il (* stubs i as 0 *) =
                List.map (fun x -> mk_exp
                            (Econst (Initial.mk_static_int 0))
                            ~ct_annot:(Some(Ck(base_ck)))
                            Initial.tint
          ~linearity:Linearity.Ltop
                         ) nl
              in
              typing_app h base_ck pat op (pargs@args@il)
          | Ifold | Imapfold ->
              (* clocking node with equality constaint on last input and last output *)
              let ct = typing_app h base_ck pat op (pargs@args) in
              Misc.optional (unify (Ck(Clocks.last_clock ct)))
                (Misc.last_element args).e_ct_annot;
              ct
          | Ifoldi -> (* clocking the node with the extra i and last in/out constraints *)
              let il (* stubs i as 0 *) =
                List.map (fun x -> mk_exp
                            (Econst (Initial.mk_static_int 0))
                            ~ct_annot:(Some(Ck(base_ck)))
                            Initial.tint
          ~linearity:Linearity.Ltop
                         ) nl
              in
              let rec insert_i args = match args with
                | [] -> il
                | [l] -> il @ [l]
                | h::l -> h::(insert_i l)
              in
              let ct = typing_app h base_ck pat op (pargs@(insert_i args)) in
              Misc.optional (unify (Ck (Clocks.last_clock ct)))
                (Misc.last_element args).e_ct_annot;
              ct
        in
        ct, base_ck
    | Esplit _ | Elast _ -> assert false
  in
  begin match e.e_ct_annot with
    None -> ()
  | Some e_ct ->
      try
        unify ct e_ct
      with Unify ->
        eprintf "Incoherent clock annotation.@\n";
        error_message e.e_loc (Etypeclash (ct,e_ct));
  end;
  e.e_ct_annot <- Some(ct);
  ct, base

and expect h pat expected_ct e =
  let actual_ct,base = typing h pat e in
  (try unify actual_ct expected_ct
   with Unify -> error_message e.e_loc (Etypeclash (actual_ct, expected_ct)))

and typing_app h base pat op e_list = match op with
  | Etuple (* to relax ? *)
  | Ebang
  | Earrow
  | Efun _ (* stateless functions: inputs and outputs on the same clock *) (*TODO really ??*)
  | Earray_fill | Eselect | Eselect_dyn | Eselect_trunc | Eupdate
  | Eselect_slice | Econcat | Earray | Efield | Efield_update | Eifthenelse | Ereinit ->
      List.iter (expect h pat (Ck base)) e_list;
      Ck base
  | Enode f ->
      let node = Modules.find_value f in
      let pat_id_list = ident_list_of_pat pat in
      let rec build_env a_l v_l env = match a_l, v_l with
        | [],[] -> env
        | a::a_l, v::v_l -> (match a.a_name with
          | None -> build_env a_l v_l env
          | Some n -> build_env a_l v_l ((n,v)::env))
        | _ ->
            Printf.printf "Fun/node : %s\n" (Names.fullname f);
            Misc.internal_error "Clocking, non matching signature"
      in
      let env_pat = build_env node.node_outputs pat_id_list [] in
      let env_args = build_env node.node_inputs e_list [] in
      (* implement with Cbase as base, replace name dep by ident dep *)
      let rec sigck_to_ck sck = match sck with
        | Signature.Cbase -> base
        | Signature.Con (sck,c,x) ->
            (* find x in the envs : *)
            let id = try List.assoc x env_pat
                     with Not_found ->
                       try
                         let e = List.assoc x env_args in
                         (match e.e_desc with
                           | Evar id -> id
                           | _ -> error_message e.e_loc Edefclock)
                       with Not_found ->
                         Misc.internal_error "Clocking, non matching signature 2"
            in
            Clocks.Con (sigck_to_ck sck, c, id)
      in
      List.iter2
        (fun a e -> expect h pat (Ck(sigck_to_ck a.a_clock)) e)
        node.node_inputs e_list;
      Clocks.prod (List.map (fun a -> sigck_to_ck a.a_clock) node.node_outputs)

let append_env h vds =
  List.fold_left (fun h { v_ident = n; v_clock = ck } -> Env.add n ck h) h vds

let rec typing_eq h ({ eq_desc = desc; eq_loc = loc } as eq) =
  match desc with
  | Eeq(pat,e) ->
      let ct,_ = typing h pat e in
      let pat_ct = typing_pat h pat in
      (try unify ct pat_ct
       with Unify ->
         eprintf "Incoherent clock between right and left side of the equation.@\n";
         error_message loc (Etypeclash (ct, pat_ct)))
  | Eblock b ->
      ignore(typing_block h b)
  | _ -> assert false

and typing_eqs h eq_list = List.iter (typing_eq h) eq_list

and typing_block h
    ({ b_local = l; b_equs = eq_list; b_loc = loc } as b) =
  let h' = append_env h l in
  typing_eqs h' eq_list;
  h'

let typing_contract h contract =
  match contract with
    | None -> h
    | Some { c_block = b;
             c_assume = e_a;
             c_enforce = e_g;
             c_controllables = c_list } ->
        let h' = typing_block h b in
        (* assumption *)
        expect h' (Etuplepat []) (Ck Cbase) e_a;
        (* property *)
        expect h' (Etuplepat []) (Ck Cbase) e_g;
        append_env h c_list

(* check signature causality and update it in the global env *)
let update_signature h node =
  let set_arg_clock vd ad =
    { ad with a_clock = Clocks.ck_to_sck (ck_repr (Env.find vd.v_ident h)) }
  in
  let sign = Modules.find_value node.n_name in
  let sign =
    { sign with node_inputs = List.map2 set_arg_clock node.n_input sign.node_inputs;
                node_outputs = List.map2 set_arg_clock node.n_output sign.node_outputs } in
  Check_signature.check_signature sign;
  Modules.replace_value node.n_name sign

let typing_node node =
  let h0 = append_env Env.empty node.n_input in
  let h0 = append_env h0 node.n_output in
  let h = typing_contract h0 node.n_contract in
  typing_block h node.n_block;
  (* synchronize input and output on base : find the free vars and set them to base *)
  Env.iter (fun _ ck -> unify_ck Cbase (root_ck_of ck)) h0;
  (*update clock info in variables descriptions *)
  let set_clock vd = { vd with v_clock = ck_repr (Env.find vd.v_ident h) } in
  let node = { node with n_input = List.map set_clock node.n_input;
                         n_output = List.map set_clock node.n_output }
  in
  (* check signature causality and update it in the global env *)
  update_signature h node;
  node

let program p =
  let program_desc pd = match pd with
    | Pnode nd -> Pnode (typing_node nd)
    | _ -> pd
  in
    { p with p_desc = List.map program_desc p.p_desc; }

