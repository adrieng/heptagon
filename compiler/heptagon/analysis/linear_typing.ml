open Linearity
open Idents
open Names
open Location
open Misc
open Signature
open Modules
open Heptagon

type error =
  | Eunify_failed_one of linearity
  | Eunify_failed of linearity * linearity
  | Earg_should_be_linear
  | Elocation_already_defined of linearity_var
  | Elocation_already_used of linearity_var
  | Elinear_variables_used_twice of ident
  | Ewrong_linearity_for_iterator
  | Eoutput_linearity_not_declared of linearity_var
  | Emapi_bad_args of linearity
  | Ewrong_init of linearity_var * linearity

exception TypingError of error

let error kind = raise (TypingError(kind))

let message loc kind =
  begin match kind with
    | Eunify_failed_one expected_lin ->
      Format.eprintf "%aThis expression cannot have the linearity '%s'.@."
        print_location loc
        (lin_to_string expected_lin)
    | Eunify_failed (expected_lin, lin) ->
      Format.eprintf "%aFound linearity '%s' does not \
                       match expected linearity '%s'.@."
        print_location loc
        (lin_to_string lin)
        (lin_to_string expected_lin)
    | Earg_should_be_linear ->
      Format.eprintf "%aArgument should be linear.@."
        print_location loc
    | Elocation_already_defined r ->
      Format.eprintf "%aMemory location '%s' is already defined.@."
        print_location loc
        r
    | Elocation_already_used r ->
      Format.eprintf "%aThe memory location '%s' cannot be \
               used more than once in the same function call.@."
        print_location loc
        r
    | Elinear_variables_used_twice id ->
      Format.eprintf "%aVariable '%s' is semilinear and cannot be used twice@."
        print_location loc
        (name id)
    | Ewrong_linearity_for_iterator ->
      Format.eprintf "%aA function of this linearity \
             cannot be used with this iterator.@."
        print_location loc
    | Eoutput_linearity_not_declared r ->
      Format.eprintf "%aThe memory location '%s' cannot be \
        used in an output without being declared in an input.@."
        print_location loc
        r
    | Emapi_bad_args lin ->
        Format.eprintf
          "%aThe function given to mapi should expect a non linear \
               variable as the last argument (found: %a).@."
          print_location loc
          print_linearity lin
    | Ewrong_init (r, lin) ->
        Format.eprintf
          "%aThe variable defined by init<<%s>> should correspond \
                to the given location (found: %a).@."
          print_location loc
          r
          print_linearity lin
  end;
  raise Errors.Error

module VarsCollection =
struct
  type t =
    | Vars of LinearitySet.t
    | CollectionTuple of t list

  let empty = Vars (LinearitySet.empty)
  let is_empty c =
    match c with
      | Vars s -> LinearitySet.is_empty s
      | _ -> false

  let prod = function
    | [l] -> l
    | l -> CollectionTuple l

 (* let map f = function
    | Vars l -> Vars (List.map f l)
    | CollectionTuple l -> CollectionTuple (map f l)
 *)
  let rec union c1 c2 =
    match c1, c2 with
      | Vars s1, Vars s2 -> Vars (LinearitySet.union s1 s2)
      | CollectionTuple l1, CollectionTuple l2 ->
        CollectionTuple (List.map2 union l1 l2)
      | _, _ -> assert false

  let rec var_collection_of_lin = function
    | Lat r -> Vars (LinearitySet.singleton (Lat r))
    | Ltop | Lvar _ -> Vars LinearitySet.empty
    | Ltuple l ->
      CollectionTuple (List.map var_collection_of_lin l)

  let rec unify c lin  =
    match c, lin with
      | Vars s, lin ->
        if LinearitySet.mem lin s then
          lin
        else
          raise UnifyFailed
      | CollectionTuple l, Ltuple lins ->
        Linearity.prod (List.map2 unify l lins)
      | _, _ -> assert false

  let rec find_candidate c lins =
    match lins with
      | [] -> raise UnifyFailed
      | lin::lins ->
        try
          unify c lin
        with
            UnifyFailed -> find_candidate c lins
end

(** [check_linearity loc id] checks that id has not been used linearly before.
    This function is called every time a variable is used as
    a semilinear type. *)
let check_linearity =
  let used_variables = ref IdentSet.empty in
  let add loc id =
    if IdentSet.mem id !used_variables then
      message loc (Elinear_variables_used_twice id)
    else
      used_variables := IdentSet.add id !used_variables
  in
    add

(** This function is called for every exp used as a semilinear type.
    It fails if the exp is not a variable. *)
let check_linearity_exp env e lin =
  match e.e_desc, lin with
    | Evar x, Lat _ ->
      (match Env.find x env with
        | Lat _ -> check_linearity e.e_loc x
        | _ -> ())
    | _ -> ()

let used_lin_vars = ref []
(** Checks that the linearity value has not been declared before
    (in an input, a local var or using copy operator). This makes
    sure that one linearity value is only used in one place. *)
let check_fresh_lin_var loc lin =
  let check_fresh r =
    if List.mem r !used_lin_vars then
      message loc (Elocation_already_defined r)
    else
      used_lin_vars := r::(!used_lin_vars)
  in
    match lin with
      | Lat r -> check_fresh r
      | Ltop -> ()
      | _ -> assert false

(** Returns the list of linearity values used by a list of
    variable declarations. *)
let rec used_lin_vars_list = function
  | [] -> []
  | vd::vds ->
      let l = used_lin_vars_list vds in
      (match vd.v_linearity with
        | Lat r -> r::l
        | _ -> l)

(** Substitutes linearity variables (Lvar r) with their value
    given by the map. *)
let rec subst_lin m lin_list =
  let subst_one = function
    | Lvar r ->
      (try
         Lat (NamesEnv.find r m)
       with
           _ -> Lvar r)
    | Lat _ -> assert false
    | l -> l
  in
    List.map subst_one lin_list

(** Generalises the linearities of a function. It replaces
    values (Lat r) with variables (Lvar r) to get a correct sig.
    Also checks that no variable is used twice. *)
let generalize arg_list sig_arg_list =
  let env = ref S.empty in

  let add_linearity vd =
    match vd.v_linearity with
      | Lat r ->
        if S.mem r !env then
          message vd.v_loc (Elocation_already_defined r)
        else (
          env := S.add r !env;
          Lvar r
        )
      | Ltop -> Ltop
      | _ -> assert false
  in
  let update_linearity vd ad =
    { ad with a_linearity = add_linearity vd }
  in
    List.map2 update_linearity arg_list sig_arg_list

(** [subst_from_lin (s,m) expect_lin lin] creates a map,
    mapping linearity variables to their values. [expect_lin]
    and [lin] are two lists, the first one containing the variables
    and the second one the values. *)
let subst_from_lin (s,m) expect_lin lin =
  match expect_lin, lin with
    | Ltop, Ltop -> s,m
    | Lvar r1, Lat r2 ->
      if S.mem r2 s then
        message no_location (Elocation_already_used r2)
      else (
        (* Format.printf "Found mapping from _%s to %s\n" r1 r2;  *)
        S.add r2 s, NamesEnv.add r1 r2 m
      )
    | _, _ -> s,m

let rec not_linear_for_exp e =
  lin_skeleton Ltop e.e_ty

let check_init loc init lin =
  let check_one init lin = match init with
  | Lno_init -> lin
  | Linit_var r ->
      (match lin with
        | Lat r1 when r = r1 -> check_fresh_lin_var loc lin; Ltop
        | Lvar r1 when r = r1 -> check_fresh_lin_var loc lin; Ltop
        | _ -> message loc (Ewrong_init (r, lin)))
  | Linit_tuple _ -> assert false
  in
    match init, lin with
      | Linit_tuple il, Ltuple ll ->
          Ltuple (List.map2 check_one il ll)
      | _, _ -> check_one init lin

(** [unify_collect collect_list lin_list coll_exp] returns a list of linearities
    to use when a choice is possible (eg for a map). It collects the possible
    values for all args and then tries to map them to the expected values.
    [collect_list] is a list of possibilities for each arg (the list of
    linearity vars this arg can have).
    [lin_list] is the list of all linearities that are expected.
    [coll_exp] is the list of args expressions. *)
let unify_collect collect_list lin_list coll_exp =
  let rec unify_collect collect_list lin_list coll_exp =
    match collect_list, coll_exp with
      | [], [] ->
        (match lin_list with
          | [] -> []
          | _ -> raise UnifyFailed)
      | collect::collect_list, e::coll_exp ->
        (try
           (* find if this arg can be assigned one of the expected value*)
           let l = VarsCollection.find_candidate collect lin_list in
           (* and iterate on the rest of the value*)
           let lin_list = List.filter (fun l2 -> l2 <> l) lin_list in
             l::(unify_collect collect_list lin_list coll_exp)
         with UnifyFailed ->
           (* this arg cannot have any of the expected linearity,
              so it is not linear*)
           (not_linear_for_exp e)::
             (unify_collect collect_list lin_list coll_exp))
      | _, _ -> assert false
  in
  (* Remove Ltop elements from a linearity list. *)
  let rec remove_nulls = function
    | [] -> []
    | l::lins ->
      let lins = remove_nulls lins in
        if is_not_linear l then lins
        else l::lins
  in
    unify_collect collect_list (remove_nulls lin_list) coll_exp

(** Returns the lists of possible types for iterator outputs.
    Basically, each output can have the linearity of any input of the same type.
    [collect_list] is the list of collected lists for each input. *)
let collect_iterator_outputs inputs outputs collect_list =
  let collect_for_type ty l arg_ty collect =
    if arg_ty = ty then VarsCollection.union collect l else l
  in
  let collect_one_output ty =
    List.fold_left2 (collect_for_type ty)
      VarsCollection.empty inputs collect_list
  in
    List.map collect_one_output outputs

(** Same as List.assoc but with two lists for the keys and values. *)
let rec assoc_lists v l1 l2 =
  match l1, l2 with
    | [], [] -> raise Not_found
    | x::l1, y::l2 ->
      if x = v then y else assoc_lists v l1 l2
    | _, _ -> assert false

(** Returns the possible linearities for the outputs of a function.
    It just matches outputs with the corresponding inputs in case of targeting,
    and returns an empty collection otherwise.
*)
let rec collect_outputs inputs collect_list outputs =
  match outputs with
    | [] -> []
    | lin::outputs ->
      let lin = (match lin with
        | Ltop -> VarsCollection.empty
        | Lvar _ -> assoc_lists lin inputs collect_list
        | _ -> assert false
      ) in
        lin::(collect_outputs inputs collect_list outputs)

let build vds env =
  List.fold_left (fun env vd -> Env.add vd.v_ident vd.v_linearity env) env vds

(** [extract_lin_exp args_lin e_list] returns the linearities
    and expressions from e_list that are not yet set to Lat r.*)
let rec extract_lin_exp args_lin e_list =
  match args_lin, e_list with
     | [], [] -> [], []
    | arg_lin::args_lin, e::e_list ->
      let lin_l, l = extract_lin_exp args_lin e_list in
        (match arg_lin with
          | Lat _ -> lin_l, l
          | lin -> lin::lin_l, e::l)
    | _, _ -> assert false

(** [fuse_args_lin args_lin collect_lins] fuse the two lists,
    taking elements from the first list if it semilinear (Lat r)
    and from the second list otherwise. *)
let rec fuse_args_lin args_lin collect_lins =
  match args_lin, collect_lins with
    | [], [] -> []
    | [], _ -> assert false
    | args_lin, [] -> args_lin
    | (Lat r)::args_lin, collect_lins ->
      (Lat r)::(fuse_args_lin args_lin collect_lins)
    | _::args_lin, x::collect_lins ->
      x::(fuse_args_lin args_lin collect_lins)

(** [extract_not_lin_var_exp args_lin e_list] returns the linearities
    and expressions from e_list that are not yet set to Lvar r.*)
let rec extract_not_lin_var_exp args_lin e_list =
  match args_lin, e_list with
    | [], [] -> [], []
    | arg_lin::args_lin, e::e_list ->
      let lin_l, l = extract_lin_exp args_lin e_list in
        (match arg_lin with
          | Lvar _ -> lin_l, l
          | lin -> lin::lin_l, e::l)
    | _, _ -> assert false

(** [fuse_iterator_collect fixed_coll free_coll] fuse the two lists,
    taking elements from the first list if it not empty
    and from the second list otherwise. *)
let rec fuse_iterator_collect fixed_coll free_coll =
  match fixed_coll, free_coll with
    | [], [] -> []
    | [], _ -> assert false
    | fixed_coll, [] -> fixed_coll
    | coll::fixed_coll, x::free_coll ->
      if VarsCollection.is_empty coll then
        x::(fuse_iterator_collect fixed_coll free_coll)
      else
        coll::(fuse_iterator_collect fixed_coll (x::free_coll))

let rec typing_pat env = function
  | Evarpat n -> Env.find n env
  | Etuplepat l ->
      prod (List.map (typing_pat env) l)

(** Linear typing of expressions. This function should not be called directly.
    Use expect instead, as typing of some expressions need to know
    the expected linearity. *)
let rec typing_exp env e =
  let l = match e.e_desc with
    | Econst _ -> Ltop
    | Evar x -> Env.find x env
    | Elast _ -> Ltop
    | Epre (_, e) ->
      let lin = (not_linear_for_exp e) in
        safe_expect env lin e; lin
    | Efby (e1, e2) ->
      safe_expect env (not_linear_for_exp e1) e1;
      safe_expect env (not_linear_for_exp e1) e2;
      not_linear_for_exp e1
    | Eapp ({ a_op = Efield }, _, _) -> Ltop
    | Eapp ({ a_op = Earray }, _, _) -> Ltop
    | Estruct _ -> Ltop
    | Emerge _ | Ewhen _ | Eapp _ | Eiterator _ -> assert false
  in
    e.e_linearity <- l;
    l

(** Returns the possible linearities of an expression. *)
and collect_exp env e =
  match e.e_desc with
    | Eapp ({ a_op = Etuple }, e_list, _) ->
      VarsCollection.prod (List.map (collect_exp env) e_list)
    | Eapp({ a_op = op }, e_list, _) -> collect_app env op e_list
    | Eiterator (it, { a_op = Enode f | Efun f }, _, _, e_list, _) ->
      let ty_desc = Modules.find_value f in
        collect_iterator env it ty_desc e_list
    | _ -> VarsCollection.var_collection_of_lin (typing_exp env e)

and collect_iterator env it ty_desc e_list = match it with
  | Imap | Imapi ->
    let inputs_lins = linearities_of_arg_list ty_desc.node_inputs in
    let inputs_lins = if it = Imapi then fst (split_last inputs_lins) else inputs_lins in
    let outputs_lins = linearities_of_arg_list ty_desc.node_outputs in
    let collect_list = List.map (collect_exp env) e_list in
    (* first collect outputs fixed by the function's targeting*)
    let collect_outputs =
      collect_outputs inputs_lins collect_list outputs_lins in
   (* then collect remaining outputs*)
    let free_out_lins, _ = extract_not_lin_var_exp outputs_lins outputs_lins in
    let free_in_lins, collect_free =
      extract_not_lin_var_exp inputs_lins collect_list in
    let free_outputs =
      collect_iterator_outputs free_in_lins free_out_lins collect_free in
      (*mix the two lists*)
      VarsCollection.prod (fuse_iterator_collect collect_outputs free_outputs)

  | Imapfold ->
    let e_list, acc = split_last e_list in
    let inputs_lins, _ =
      split_last (linearities_of_arg_list ty_desc.node_inputs) in
    let outputs_lins, _ =
      split_last (linearities_of_arg_list ty_desc.node_outputs) in
    let collect_list = List.map (collect_exp env) e_list in
    let collect_acc = collect_exp env acc in
    (* first collect outputs fixed by the function's targeting*)
    let collect_outputs =
      collect_outputs inputs_lins collect_list outputs_lins in
    (* then collect remaining outputs*)
    let free_out_lins, _ = extract_not_lin_var_exp outputs_lins outputs_lins in
    let free_in_lins, collect_free =
      extract_not_lin_var_exp inputs_lins collect_list in
    let free_outputs =
      collect_iterator_outputs free_in_lins free_out_lins collect_free in
      (*mix the two lists*)
      VarsCollection.prod
        ((fuse_iterator_collect collect_outputs free_outputs)@[collect_acc])

  | Ifold ->
    collect_exp env (last_element e_list)

  | Ifoldi ->
    assert false (* TODO *)

(** Returns the possible linearities of an application. *)
and collect_app env op e_list = match op with
  | Eifthenelse->
    let _, e2, e3 = assert_3 e_list in
      VarsCollection.union (collect_exp env e2) (collect_exp env e3)

  | Efun f | Enode f ->
    let ty_desc = Modules.find_value f in
    let inputs_lins = linearities_of_arg_list ty_desc.node_inputs in
    let outputs_lins = linearities_of_arg_list ty_desc.node_outputs in
    let collect_list = List.map (collect_exp env) e_list in
      VarsCollection.prod
        (collect_outputs inputs_lins collect_list outputs_lins)

  | _ -> VarsCollection.var_collection_of_lin (typing_app env op e_list)

and typing_args env expected_lin_list e_list =
  List.iter2 (fun elin e -> safe_expect env elin e) expected_lin_list e_list

and typing_app env op e_list = match op with
  | Earrow ->
    let e1, e2 = assert_2 e_list in
      safe_expect env Ltop e1;
      safe_expect env Ltop e2;
      Ltop
  | Earray_fill | Eselect | Eselect_slice ->
    let e = assert_1 e_list in
      safe_expect env Ltop e;
      Ltop
  | Eselect_dyn ->
    let e1, defe, idx_list = assert_2min e_list in
      safe_expect env Ltop e1;
      safe_expect env Ltop defe;
      List.iter (safe_expect env Ltop) idx_list;
      Ltop
  | Eselect_trunc ->
    let e1, idx_list = assert_1min e_list in
      safe_expect env Ltop e1;
      List.iter (safe_expect env Ltop) idx_list;
      Ltop
  | Econcat ->
    let e1, e2 = assert_2 e_list in
      safe_expect env Ltop e1;
      safe_expect env Ltop e2;
      Ltop
  | Earray ->
    List.iter (safe_expect env Ltop) e_list;
    Ltop
  | Efield ->
    let e = assert_1 e_list in
      safe_expect env Ltop e;
      Ltop
  | Eequal ->
    List.iter (safe_expect env Ltop) e_list;
    Ltop
  | Eifthenelse | Efun _ | Enode _ | Etuple
  | Eupdate | Efield_update -> assert false (*already done in expect_app*)

(** Check that the application of op to e_list can have the linearity
    expected_lin. *)
and expect_app env expected_lin op e_list = match op with
  | Efun f | Enode f ->
    let ty_desc = Modules.find_value f in
    let inputs_lins = linearities_of_arg_list ty_desc.node_inputs in
    let outputs_lins = linearities_of_arg_list ty_desc.node_outputs in
    let expected_lin_list = linearity_list_of_linearity expected_lin in
    (* create the map that matches linearity variables to linearity values
       from the ouputs and the expected lin*)
    let m = snd ( List.fold_left2 subst_from_lin
                    (S.empty, NamesEnv.empty) outputs_lins expected_lin_list) in
    (* and apply it to the inputs*)
    let inputs_lins = subst_lin m inputs_lins in
      (* and check that it works *)
      typing_args env inputs_lins e_list;
      unify_lin expected_lin (prod outputs_lins)

    | Eifthenelse ->
      let e1, e2, e3 = assert_3 e_list in
        safe_expect env Ltop e1;
        let c2 = collect_exp env e2 in
        let c3 = collect_exp env e3 in
        let l2, l3 = assert_2 (unify_collect [c2;c3] [expected_lin] [e2;e3]) in
          safe_expect env l2 e2;
          safe_expect env l3 e3;
          expected_lin

    | Efield_update ->
      let e1, e2 = assert_2 e_list in
        safe_expect env Ltop e2;
        expect env expected_lin e1

    | Eupdate ->
      let e1, e2, idx = assert_2min e_list in
        safe_expect env Ltop e2;
        List.iter (safe_expect env Ltop) idx;
        expect env expected_lin e1

    | _ ->
      let actual_lin = typing_app env op e_list in
        unify_lin expected_lin actual_lin

(** Checks the typing of an accumulator. It also checks
    that the function has a targeting compatible with the iterator. *)
and typing_accumulator env acc acc_in_lin acc_out_lin
    expected_acc_lin inputs_lin =
  (match acc_out_lin with
     | Lvar _ ->
       if List.mem acc_out_lin inputs_lin then
         message acc.e_loc Ewrong_linearity_for_iterator
     | _ -> ()
  );

  let m = snd (subst_from_lin (S.empty, NamesEnv.empty)
                 acc_out_lin expected_acc_lin) in
  let acc_lin = assert_1 (subst_lin m [acc_in_lin]) in
    safe_expect env acc_lin acc

and expect_iterator env loc it expected_lin inputs_lins outputs_lins e_list = match it with
  | Imap | Imapi ->
    (* First find the linearities fixed by the linearities of the
       iterated function. *)
    let inputs_lins, idx_lin = if it = Imapi then split_last inputs_lins else inputs_lins, Ltop in

    let m = snd ( List.fold_left2 subst_from_lin
                    (S.empty, NamesEnv.empty) outputs_lins expected_lin) in
    let inputs_lins = subst_lin m inputs_lins in

    (* Then guess linearities of other vars to get expected_lin *)
    let _, coll_exp = extract_lin_exp inputs_lins e_list in
    let collect_list = List.map (collect_exp env) coll_exp in
    let names_list =
      List.filter (fun x -> not (List.mem x inputs_lins)) expected_lin in
    let collect_lin = unify_collect collect_list names_list coll_exp in
    let inputs_lins = fuse_args_lin inputs_lins collect_lin in

      (* The index should not be linear *)
      if it = Imapi then (
        try ignore (unify_lin idx_lin Ltop)
        with UnifyFailed -> message loc (Emapi_bad_args idx_lin));

      (*Check that the args have the wanted linearity*)
      typing_args env inputs_lins e_list;
      prod expected_lin

  | Imapfold ->
    (* Check the linearity of the accumulator*)
    let e_list, acc = split_last e_list in
    let inputs_lins, acc_in_lin = split_last inputs_lins in
    let outputs_lins, acc_out_lin = split_last outputs_lins in
    let expected_lin, expected_acc_lin = split_last expected_lin in
      typing_accumulator env acc acc_in_lin acc_out_lin
        expected_acc_lin inputs_lins;

      (* First find the linearities fixed by the linearities of the
         iterated function. *)
      let m = snd ( List.fold_left2 subst_from_lin
                      (S.empty, NamesEnv.empty) outputs_lins expected_lin) in
      let inputs_lins = subst_lin m inputs_lins in

      (* Then guess linearities of other vars to get expected_lin *)
      let _, coll_exp = extract_lin_exp inputs_lins e_list in
      let collect_list = List.map (collect_exp env) coll_exp in
      let names_list =
        List.filter (fun x -> not(List.mem x inputs_lins)) expected_lin in
      let collect_lin = unify_collect collect_list names_list coll_exp in
      let inputs_lins = fuse_args_lin inputs_lins collect_lin in

        (*Check that the args have the wanted linearity*)
        typing_args env inputs_lins e_list;
        prod (expected_lin@[expected_acc_lin])

    | Ifold ->
      let e_list, acc = split_last e_list in
      let inputs_lins, acc_in_lin = split_last inputs_lins in
      let _, acc_out_lin = split_last outputs_lins in
      let _, expected_acc_lin = split_last expected_lin in
        ignore (List.map (safe_expect env Ltop) e_list);
        typing_accumulator env acc acc_in_lin acc_out_lin
          expected_acc_lin inputs_lins;
        expected_acc_lin

    | Ifoldi ->
      let e_list, acc = split_last e_list in
      let inputs_lins, acc_in_lin = split_last inputs_lins in
      let inputs_lins, _ = split_last inputs_lins in
      let _, acc_out_lin = split_last outputs_lins in
      let _, expected_acc_lin = split_last expected_lin in
        ignore (List.map (safe_expect env Ltop) e_list);
        typing_accumulator env acc acc_in_lin acc_out_lin
          expected_acc_lin inputs_lins;
        expected_acc_lin

and typing_eq env eq =
  match eq.eq_desc with
    | Eautomaton(state_handlers) ->
        List.iter (typing_state_handler env) state_handlers
    | Eswitch(e, switch_handlers) ->
        safe_expect env Ltop e;
        List.iter (typing_switch_handler env) switch_handlers
    | Epresent(present_handlers, b) ->
        List.iter (typing_present_handler env) present_handlers;
        ignore (typing_block env b)
    | Ereset(b, e) ->
        safe_expect env Ltop e;
        ignore (typing_block env b)
    | Eeq(pat, e) ->
        let lin_pat = typing_pat env pat in
        let lin_pat = check_init eq.eq_loc eq.eq_inits lin_pat in
          safe_expect env lin_pat e
    | Eblock b ->
        ignore (typing_block env b)

and typing_state_handler env sh =
  let env = typing_block env sh.s_block  in
    List.iter (typing_escape env) sh.s_until;
    List.iter (typing_escape env) sh.s_unless;

and typing_escape env esc =
  safe_expect env Ltop esc.e_cond

and typing_block env block =
  let env = build block.b_local env in
    List.iter (typing_eq env) block.b_equs;
    env

and typing_switch_handler env sh =
  ignore (typing_block env sh.w_block)

and typing_present_handler env ph =
  safe_expect env Ltop ph.p_cond;
  ignore (typing_block env ph.p_block)

and expect env lin e =
  let l = match e.e_desc with
    | Evar x ->
      let actual_lin = Env.find x env in
        check_linearity_exp env e lin;
        unify_lin lin actual_lin

    | Emerge (c, c_e_list) ->
        safe_expect env Ltop c;
        List.iter (fun (_, e) -> safe_expect env lin e) c_e_list;
        lin

    | Ewhen (e, _, x) ->
        safe_expect env Ltop x;
        expect env lin e

    | Eapp ({ a_op = Etuple }, e_list, _) ->
      let lin_list = linearity_list_of_linearity lin in
        (try
          prod (List.map2 (expect env) lin_list e_list)
        with
            Invalid_argument _ -> message e.e_loc (Eunify_failed_one lin))

    | Eapp({ a_op = op }, e_list, _) ->
      (try
         expect_app env lin op e_list
       with
           UnifyFailed -> message e.e_loc (Eunify_failed_one lin))

    | Eiterator (it, { a_op = Enode f | Efun f }, _, pe_list, e_list, _) ->
      let ty_desc = Modules.find_value f in
      let expected_lin_list = linearity_list_of_linearity lin in
      let inputs_lins = linearities_of_arg_list ty_desc.node_inputs in
      let _, inputs_lins = Misc.split_at (List.length pe_list) inputs_lins in
      let outputs_lins = linearities_of_arg_list ty_desc.node_outputs in
        List.iter (fun e -> safe_expect env (not_linear_for_exp e) e) pe_list;
        (try
           expect_iterator env e.e_loc it expected_lin_list inputs_lins outputs_lins e_list
         with
             UnifyFailed -> message e.e_loc (Eunify_failed_one lin))

    | _ ->
      let actual_lin = typing_exp env e in
        unify_lin lin actual_lin
  in
    e.e_linearity <- l;
    l

and safe_expect env lin e =
  begin try
    ignore (expect env lin e)
  with
      UnifyFailed -> message e.e_loc (Eunify_failed_one (lin))
  end

let check_outputs inputs outputs =
  let add_linearity env vd =
    match vd.v_linearity with
      | Lat r -> S.add r env
      | _ -> env
  in
  let check_out env vd =
    match vd.v_linearity with
      | Lat r ->
        if not (S.mem r env) then
          message vd.v_loc (Eoutput_linearity_not_declared r)
      | _ -> ()
  in
  let env = List.fold_left add_linearity S.empty inputs in
    List.iter (check_out env) outputs

let node f =
  used_lin_vars := used_lin_vars_list (f.n_input);

  let env = build (f.n_input @ f.n_output) Env.empty in
    ignore (typing_block env f.n_block);
    check_outputs f.n_input f.n_output;

    (* Update the function signature *)
    let sig_info = Modules.find_value f.n_name in
    let sig_info =
      { sig_info with
        node_inputs = generalize f.n_input sig_info.node_inputs;
        node_outputs = generalize f.n_output sig_info.node_outputs } in
      Modules.replace_value f.n_name sig_info

let program ({ p_desc = pd } as p) =
  List.iter (function Pnode n -> node n | _ -> ()) pd;
  p

