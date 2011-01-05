(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

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
open Pp_tools
open Mls_compare

(** TODO: remove all references to Introvars *)

let debug_do = Introvars.debug_do

module IntMap = Map.Make(struct
                           type t = int
                           let compare = Pervasives.compare
                         end)

let ident_of_int =
  let ht = Hashtbl.create 300 in
  fun (name : string) (i : int) ->
    try Hashtbl.find ht i
    with Not_found ->
      let new_ident = Idents.gen_var "tomato" name in
      Hashtbl.add ht i new_ident;
      new_ident

type cl_id =
  | Input of ident
  | Var of int
  | Pattern of pat * int list

let print_cl_id fmt cl_id = match cl_id with
  | Input ident -> Format.fprintf fmt "in %a" print_ident ident
  | Var i -> Format.fprintf fmt "%d" i
  | Pattern (pat, il) ->
      Format.fprintf fmt "%a: %a"
        print_pat pat
        (print_list_r (fun fmt d -> Format.fprintf fmt "%d" d) "" "," "") il

let cl_id_compare id1 id2 = match id1, id2 with
  | Input id1, Input id2 -> ident_compare id1 id2
  | Var i1, Var i2 -> compare i1 i2
  | Pattern (p1, i1), Pattern (p2, i2) ->
      let cr = pat_compare p1 p2 in
      if cr <> 0 then cr else Pervasives.compare i1 i2
  | (Input _ | Var _), _ -> -1
  | Pattern _, _ -> 1

module PatEnv =
  struct
    module P = Map.Make(struct
                          type t = pat
                          let compare = pat_compare
                        end)

    type penv_t = (int * exp * ident list) P.t


    (* An environment used for automata minimization: holds both a pattern environment mapping patterns to equivalence
       classes, and a [(pat * int list) Env.t] that maps variable [x] to a [(pat, pth)] tuple where [pat] is the pattern
       holding [x] at path [pth] *)
    type t = penv_t * (pat * int list) Env.t

    let empty = (P.empty, Env.empty)

    let find ident (penv, _) = P.find ident penv

    let fold f (penv, _) acc = P.fold f penv acc

    let find_class_id (penv, env) ident =
      try let (cl_id, _, _) = P.find (Evarpat ident) penv in Var cl_id
      with Not_found ->
        (try let pat, i = Env.find ident env in Pattern (pat, i)
         with Not_found -> Input ident)

    let find_id ident (penv, env) =
      try P.find (Evarpat ident) penv
      with Not_found ->
        let rec consume (pat, i_list) = match pat, i_list with
          | Evarpat ident, [] -> Evarpat ident
          | Etuplepat pat_list, x :: i_list ->
              consume (List.nth pat_list x, i_list)
          | Etuplepat _, [] | Evarpat _, _ :: _ -> assert false in
        P.find (consume (Env.find ident env)) penv

    let print fmt (penv, env) =
      let print_binding pat (cl_num, head, children) =
        Format.fprintf fmt
          " @[<v 2>%a => class %d, head = @[%a@], children = @[%a@]@]@\n"
          print_pat pat
          cl_num
          print_exp head
          (print_list_l print_ident "" "," "") children

      and print_pat_link ident (pat, i) =
        Format.fprintf fmt " @[<v 2>%a => %a, %a@]@\n"
          print_ident ident
          print_pat pat
          (print_list_r (fun fmt i -> Format.fprintf fmt "%d" i) "" "," "") i in
      P.iter print_binding penv;
      Env.iter print_pat_link env

    let add ident info (penv, env) = (P.add ident info penv, env)

    let add_pat_link (penv, env) pat =
      let rec add path pat env = match pat with
        | Evarpat ident -> Env.add ident path env
        | Etuplepat pat_list ->
            let rec call pat (i, env) = (i + 1, add (i :: path) pat env) in
            snd (List.fold_right call pat_list (0, env)) in
      (penv, add [] pat env)
  end

module SubstNode =
struct
  let apply_subst subst ident =
    try match PatEnv.find_id ident subst with
      | Evarpat ident -> ident
      | pat ->
          debug_do (fun _ ->
                      Format.printf "apply_subst (...) %a => %a@."
                        print_ident ident
                        print_pat pat);
          assert false
    with Not_found -> ident

  let rec apply_subst_clock subst ck = match ck with
    | Cbase -> Cbase
    | Con (ck, cstr, x) ->
        Con (apply_subst_clock subst ck, cstr, apply_subst subst x)
    | Cvar { contents = Clink ck; } -> apply_subst_clock subst ck
    | Cvar { contents = Cindex _; } -> ck


  let exp funs subst e =
    let (e, subst) = Mls_mapfold.exp funs subst e in
    ({ e with e_ck = apply_subst_clock subst e.e_ck; }, subst)

  let var_dec _ subst vd =
    ({ vd with v_ident = apply_subst subst vd.v_ident; }, subst)

  let subst_node subst nd =
    let funs = { Mls_mapfold.defaults with
                   Mls_mapfold.exp = exp;
                   Mls_mapfold.var_dec = var_dec; } in
    fst (Mls_mapfold.node_dec_it funs subst nd)
end

let empty_var = Idents.gen_var "tomato" "EMPTY"
let dummy_exp = mk_exp Types.Tinvalid (Evar empty_var)

let exp_of_ident ~ty vi = mk_exp ~ty:ty (Evar vi)
and ident_of_exp { e_desc = e_d; } = match e_d with
  | Evar vi -> vi
  | _ -> invalid_arg "ident_of_exp"

let behead e =
  (* We have to add rst as a sub-expression for finer equivalence classes
     computation for Eapps and Eiterators:

     x = f() every m;
     y = f() every n;

     should be equivalent iff m and n are. Thus, when beheading e, we have to
     somehow record whether it held a reset field or not. We choose to do
     so by adding an [empty_var] as a reset. In our example, x and y
     become:

     x = {f() every $empty_var}, m
     y = {f() every $empty_var}, n
  *)

  let encode_reset rst = match rst with
    | None -> (None, [])
    | Some x -> (Some empty_var, [exp_of_ident ~ty:(Tid Initial.pbool) x]) in

  let (e_desc, children) = match e.e_desc with
    | Econst _ -> (e.e_desc, [])
    | Evar _ -> (e.e_desc, [])
    | Efby (c, e) -> (Efby (c, dummy_exp), [e])
    | Eapp (op, e_list, rst) ->
        let (rst, l) = encode_reset rst in
        (* the pretty-printer dies when handling certain kinds of apps with
           an empty argument list. *)
        (Eapp (op, repeat_list dummy_exp (List.length e_list), rst), l @ e_list)
    | Ewhen (e, cstr, x) ->
        (Ewhen (dummy_exp, cstr, empty_var), [exp_of_ident ~ty:(Modules.find_constrs cstr)  x; e])
    | Emerge (x, lne_list) ->
        let (lne_list, e_list) = List.split (List.map (fun (ln, e) -> ((ln, dummy_exp), e)) lne_list) in
        let ty = lne_list |> List.hd |> fun (c,_) -> c |> Modules.find_constrs in
        (Emerge (empty_var, lne_list), exp_of_ident ~ty:ty x::e_list)
    | Estruct lne_list ->
        let (lne_list, e_list) =
          List.split
            (List.map (fun (ln, e) -> ((ln, dummy_exp), e)) lne_list) in
        (Estruct lne_list, e_list)
    | Eiterator (it, op, s, pe_list, e_list, rst) ->
        let (rst, l) = encode_reset rst in
        (* count is the number of partial arguments *)
        let count = mk_exp ~ty:Initial.tint
          (Econst (Initial.mk_static_int (List.length pe_list))) in
        (Eiterator (it, op, s, [], [], rst), count :: (pe_list @ l @ e_list)) in
  ({ e with e_desc = e_desc; }, children)

let pat_name pat =
  let rec acc fmt pat = match pat with
    | Evarpat ident -> print_ident fmt ident
    | Etuplepat pat_list -> print_list acc "" "x" "" fmt pat_list in
  ignore (Format.flush_str_formatter ());
  acc Format.str_formatter pat;
  Format.flush_str_formatter ()

module ClassMap = Map.Make(
  struct
    (* class id 0 will be for inputs, which are implicitly never in the
       same class *)
    type t = (Minils.exp * cl_id list)
    let compare (e1, id1_list) (e2, id2_list) =
      let e_c = exp_compare e1 e2 in
      if e_c <> 0 then e_c else list_compare cl_id_compare id1_list id2_list
  end
)

let bindings_of_env env =
  let compare (_, (_, e1, _)) (_, (_, e2, _)) = exp_compare e1 e2 in

  let add pat info l = (pat, info) :: l in
  List.sort compare (PatEnv.fold add env [])

let normalize_classes env =
  let l = bindings_of_env env in (* key property: l is sorted by exp *)
  let _, _, l =
    let add (pat, (cl_num, e, children)) (subst, i, l) =
      try (subst, i, (pat, (IntMap.find cl_num subst, e, children)) :: l)
      with Not_found ->
        let vi = Var i in
        (IntMap.add cl_num vi subst, i + 1, (pat, (vi, e, children)) :: l) in
    List.fold_right add l (IntMap.empty, 1, []) in
  let add (key, info) env = PatEnv.P.add key info env in
  List.fold_right add l PatEnv.P.empty

let equivalent env1 env2 = (normalize_classes env1) = (normalize_classes env2)

let compute_initial_env env eq =
  let penv = match eq.eq_lhs with
    | Etuplepat _ ->
        let rec add pat i_list penv = match pat with
          | Evarpat id -> Env.add id (eq.eq_lhs, i_list) penv
          | Etuplepat pat_list ->
              fold_righti (fun i pat -> add pat (i :: i_list)) pat_list penv in
        add eq.eq_lhs [] (snd env)
    | Evarpat _ -> snd env in

  let (e, children) = behead eq.eq_rhs in
  let (e, children) = match e.e_desc, children with
    | Evar _, [] -> (dummy_exp, [e])
    | _ -> (e, children) in
  let children =
    let add e = match e.e_desc with
      | Evar id -> id
      | _ ->
          Format.printf "Unexpected: @[%a@]@."  print_exp e;
          assert false in
    List.map add children in

  let env = fst (PatEnv.add eq.eq_lhs (1, e, children) env) in
  (env, penv)

(* Idea: we put the classes in a big map, grouped by class_id = description x
   children ids. *)
let rec compute_classes (env : PatEnv.t) =
  (* Perform potential optimization, e.g. replace
     x = merge ... (true -> y) (false -> y);
     by
     x = y;
  *)
  let transform ((head, child_id_list) as cl_key) = match head.e_desc with
    | Emerge _ ->
        (* skip ident in front of the list *)
        let child_id_list = List.tl child_id_list in
        let first_elem = List.hd child_id_list in
        let all_the_same =
          List.filter (fun x -> x <> first_elem) child_id_list = [] in
        if all_the_same then (dummy_exp, [first_elem]) else cl_key
    | Eapp ({ a_op = Eifthenelse; }, _, None) ->
        (match child_id_list with
           | [_; t; e] -> if t = e then (dummy_exp, [t]) else cl_key
           | _ -> assert false)
    | _ -> cl_key in

  let clmap =
    let add_to_classmap pat ((_, head, children) as info) clmap =
      let cl_key = (head, List.map (PatEnv.find_class_id env) children) in
      let cl_key = transform cl_key in (* apply potential optimization *)
      let cl = try ClassMap.find cl_key clmap with Not_found -> [] in
      ClassMap.add cl_key ((pat, info) :: cl) clmap in
    PatEnv.fold add_to_classmap env ClassMap.empty in

  let (_, penv') =
    let add_class_to_env _ ninfo_list (i, env) =
      let add_ninfo_to_env env (pat, (_, head, children)) =
        PatEnv.P.add pat (i, head, children) env in
      (i + 1, List.fold_left add_ninfo_to_env env ninfo_list) in
    ClassMap.fold add_class_to_env clmap (1, PatEnv.P.empty) in

  let (env' : PatEnv.t) = (penv', snd env) in

  debug_do (fun _ ->
              Format.printf "New environment:@\n%a@\n" PatEnv.print env');

  if equivalent env env' then env' else compute_classes env'

let factor_classes (env : PatEnv.t) =
  let (subst, classes) =
    let add_to_env ident (cl_id, _, _) (subst, classes) =
      (* New identifier for [pat] : either the concatenation of the
         equivalence class patterns with a unique number appended OR *)
      let new_pattern = (* TODO: O(n2) *)
        let gather pat (cl_id', _, _) pat_list =
          if cl_id = cl_id' then pat :: pat_list else pat_list in

        let rec filter_pattern pat acc = match pat with
          | Evarpat id ->
              if Introvars.was_generated (Idents.name id)
              then acc else pat :: acc
          | Etuplepat pat_list ->
              (match filter_patterns pat_list with
                 | [] -> acc
                 | pat_list -> Etuplepat pat_list :: acc)

        and filter_patterns pat_list =
          List.fold_right filter_pattern pat_list [] in

        match filter_patterns (PatEnv.fold gather env []) with
          | [] -> Evarpat (ident_of_int "tom" cl_id)
          | [pat] -> pat
          | pat_list ->
              let concat pat prefix =
                let pn = pat_name pat in
                if Introvars.was_generated pn
                then prefix
                else pn ^ "_" ^ prefix in
              let prefix = List.fold_right concat pat_list "" in
              let prefix = (* chops trailing _ if needed *)
                if prefix = ""
                then "tom"
                else String.sub prefix 0 (String.length prefix - 1) in
              Evarpat (ident_of_int prefix cl_id) in
      (PatEnv.P.add ident new_pattern subst,
       IntMap.add cl_id ident classes) in
    PatEnv.fold add_to_env env (PatEnv.P.empty, IntMap.empty) in

  let create_var_for_class _ pat (penv' : PatEnv.penv_t) =
    let (cl_id, head, children) = PatEnv.find pat env in
    let children = (* remap children to new idents according to subst *)
      let remap ident =
        (* Inputs won't be present in env *)
        try match PatEnv.P.find (Evarpat ident) subst with
          | Evarpat ident' ->
              Format.printf "Remapping %a to %a@."
                print_ident ident
                print_ident ident';
              ident'
          | Etuplepat _ -> assert false
        with Not_found -> ident in
      List.map remap children in
    PatEnv.P.add (PatEnv.P.find pat subst) (cl_id, head, children) penv' in

  ((IntMap.fold create_var_for_class classes PatEnv.P.empty, snd env), subst)

let rec reconstruct input_type (env : PatEnv.t) =
  let find_head ident =
    try let (_, head, _) = PatEnv.find (Evarpat ident) env in head
    with Not_found ->
      (try
         debug_do (fun _ ->
                     Format.printf "find_head %a@." print_ident ident;
                     Env.iter
                       (fun id (p, _) ->
                          Format.printf "%a => %a@." print_ident id print_pat p)
                       (snd env));

         let (pat, _) = Env.find ident (snd env) in
         debug_do (fun _ ->
                     Format.printf "find_head %a => %a@."
                       print_ident ident
                       print_pat pat);
         let (_, head, _) = PatEnv.find pat env in head
       with Not_found -> mk_exp ~ty:(input_type ident) (Evar ident)) in

  let rec mk_var_decs pat ty var_list = match pat, ty with
    | Evarpat ident, _ -> mk_var_dec ident ty :: var_list
    | Etuplepat pat_list, Tprod ty_list ->
        List.fold_right2 mk_var_decs pat_list ty_list var_list
    | Etuplepat [], Tunit -> var_list
    | Etuplepat _, (Tarray _ | Tid _ | Tunit | Tmutable _ | Tasync _) ->
        assert false (* ill-typed *)  (* TODO async *)
  in

  let add_to_lists pat (_, head, children) (eq_list, var_list) =
    (* Remember the encoding of resets given above. *)
    let rst_of_e_list rst e_list = match rst, e_list with
      | None, _ -> (None, e_list)
      | Some empty, x :: e_list when empty == empty_var ->
          (Some (ident_of_exp x), e_list)
      | _ -> assert false in

    let make_exp child = { (find_head child) with e_desc = Evar child; }; in
    let e_desc = match head.e_desc, List.map make_exp children with
      | Econst _, [] -> head.e_desc
      | Evar _, [e] -> e.e_desc (* ILL-TYPED *)
      | Efby (seo, _), [e] -> Efby (seo, e)
      | Eapp (app, _, rst), e_list ->
          let rst, e_list = rst_of_e_list rst e_list in Eapp (app, e_list, rst)
      | Ewhen (_, cn, _), [x; e] -> Ewhen (e, cn, ident_of_exp x)
      | Emerge (_, cnel), e_list ->
          Emerge (ident_of_exp (List.hd e_list),
                  List.combine (List.map fst cnel) (List.tl e_list))
      | Estruct fnel, e_list ->
          Estruct (List.combine (List.map fst fnel) e_list)
      | Eiterator (it, app, se, [], [], rst), e_list ->
          (* the first element is the number of partial arguments *)
          let count, e_list = assert_1min e_list in
          let c = (match count.e_desc with
            | Econst { se_desc = Sint c } -> c
            | _ -> assert false)
          in
          let pe_list, e_list = Misc.split_at c e_list in
          let rst, e_list = rst_of_e_list rst e_list in
          Eiterator (it, app, se, pe_list, e_list, rst)

      | (Eiterator (_, _, _, _, _, _) | Ewhen _
        | Efby _ | Evar _ | Econst _)
          , _ -> assert false (* invariant *) in
    (mk_equation pat { head with e_desc = e_desc; } :: eq_list,
     mk_var_decs pat head.e_ty var_list) in
  PatEnv.fold add_to_lists env ([], [])

(* We may have fused together distinct outputs during minimization, e.g.

   node f(x : int) returns (o, o2 : int)
   let
     o  = 4 + x;
     o2 = 4 + x;
   tel

   becomes

   node f(x : int) returns (o_o2_42, o_o2_42 : int)
   let
     o_o2_42 = 4 + x;
   tel

   which is ill-formed. The following function reintroduces needed copies for
   duplicated outputs. In our example, f() will become:

   node f(x : int) returns (o_o2_42, o_o2_42_43 : int)
   let
     o_o2_42 = 4 + x;
     o_o2_42_43 = o_o2_42;
   tel
 *)
let introduce_copies_for_outputs nd =
  let var_dec vd (iset, vd_list, eq_list) =
    if IdentSet.mem vd.v_ident iset
    then (* introduce copy, change vd *)
      let fresh = Idents.gen_var "tomato" (Idents.name vd.v_ident) in
      let new_eq =
        let e = mk_exp ~ty:vd.v_type (Evar vd.v_ident) in
        mk_equation (Evarpat fresh) e in
      (iset, { vd with v_ident = fresh; } :: vd_list, new_eq :: eq_list)
    else
      (IdentSet.add vd.v_ident iset, vd :: vd_list, eq_list) in
  let (_, vd_list, eq_list) =
    List.fold_right var_dec nd.n_output (IdentSet.empty, [], []) in
  { nd with n_output = vd_list; n_equs = eq_list @ nd.n_equs; }

let node nd =
  debug_do (fun _ -> Format.printf "Original node:@\n%a@\n" print_node nd);

  let nd = Introvars.node nd in

  let orig_eq_count = List.length nd.n_equs in

  debug_do (fun _ ->
              Format.printf "Node with vars introduced:@\n%a@\n" print_node nd);

  let env = List.fold_left compute_initial_env PatEnv.empty nd.n_equs in

  debug_do (fun _ ->
              Format.printf "Initial environment:@\n%a@\n" PatEnv.print env);

  let env = compute_classes env in

  debug_do (fun _ ->
              Format.printf "Env with classes:@\n%a@\n" PatEnv.print env);

  let ((env : PatEnv.t), subst) = factor_classes env in

  debug_do (fun _ ->
              Format.printf "Env with factored classes:@\n%a@\n"
                PatEnv.print env);

  let eq_list, var_list =
    let input_type id =
      try
        (List.find (fun vd -> vd.v_ident = id) nd.n_input).v_type
      with Not_found ->
        Format.printf "Could not find input type for %a@." print_ident id;
        assert false in
    reconstruct input_type env in
  let var_list =
    let is_not_output vd =
      not (List.exists
             (fun out -> ident_compare vd.v_ident out.v_ident = 0)
             nd.n_output) in
    List.filter is_not_output var_list in

  let nd = { nd with n_equs = eq_list; n_local = var_list; } in
  let nd = SubstNode.subst_node (subst, snd env) nd in

  debug_do (fun _ ->
              Format.printf "TOMATOed node:@\n%a@\n" print_node nd);

  if !Compiler_options.verbose then
    Format.printf
      "TOMATO: factored out %d expressions.@."
      (orig_eq_count - List.length nd.n_equs);
(*
  let nd = Singletonvars.node nd in
*)
  debug_do (fun _ ->
              Format.printf "Factored node:@\n%a@\n" print_node nd);

  let nd = introduce_copies_for_outputs nd in

  debug_do (fun _ ->
              Format.printf "Final node:@\n%a@\n" print_node nd);

  nd

let node nd =
  let to_be_tomatoized s = s = nd.n_name in
  if List.exists to_be_tomatoized !Compiler_options.tomato_nodes
    || !Compiler_options.tomato then node nd else nd

let program p = { p with p_nodes = List.map node p.p_nodes; }

(*
let tomato_checks p =
  Checkpass.add_checks "tomato" node !Compiler_options.tomato_check p
*)
