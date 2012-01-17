open Names
open Modules
open Hept_parsetree
open Hept_parsetree_mapfold

(* Convert expressions that should be static to the corresponding
   static expression. After this pass, all the static expressions
   (including variables) are of type Econst se. *)

exception Not_static

(** Qualify a var name as a constant variable, 
    if not in local_const or global_const then raise Not_found.
    returns [true, c] if c is a fun
    returns [false, c] if c is a constant *)
let qualify_var local_const c =
  try
    let is_fun = NamesEnv.find c local_const in
    is_fun, Idents.local_qn c
  with Not_found -> (* It may be in the global environment *)
    try true, qualify_value c
    with Not_found ->
      false, qualify_const c

let assert_se e = match e.e_desc with
  | Econst se -> se
  | _ -> raise Not_static


(** convention : static params are set as the first static args,
    op<a1,a2> (a3) == op <a1> (a2,a3) == op (a1,a2,a3) *)
let static_app_from_app app args =
  match app.a_op with
    | Efun ((Q { Names.qual = Names.Pervasives }) as q)
    | Enode ((Q { Names.qual = Names.Pervasives }) as q) ->
        q, (app.a_params @ args)
    | _ -> raise Not_static

let exp funs local_const e =
  let e, _ = Hept_parsetree_mapfold.exp funs local_const e in
    try
      let sed =
        match e.e_desc with
          | Evar n ->
              (try
                let is_fun, q = qualify_var local_const n in
                if is_fun
                then Sfun (Q q)
                else Svar (Q q)
              with Not_found -> raise Not_static)
          | Eapp({ a_op = Earray_fill; a_params = n_list }, [e]) ->
              Sarray_power (assert_se e, List.map assert_se n_list)
          | Eapp({ a_op = Earray }, e_list) ->
              Sarray (List.map assert_se e_list)
          | Eapp({ a_op = Etuple }, e_list) ->
              Stuple (List.map assert_se e_list)
          | Eapp(app, e_list) ->
              let op, e_list = static_app_from_app app e_list in
              Sop (op, List.map assert_se e_list)
          | Estruct e_list ->
              Srecord (List.map (fun (f,e) -> f, assert_se e) e_list)
          | Easync e ->
              Sasync (assert_se e)
          | _ -> raise Not_static
      in
      { e with e_desc = Econst (mk_static_exp sed e.e_loc) }, local_const
    with
        Not_static -> e, local_const

let app funs local_const a =
  let a, _ = Hept_parsetree_mapfold.app funs local_const a in
  let a =
    try
      match a.a_op with
      | Enode (ToQ f) ->
          let is_fun, q = qualify_var local_const f in
          if not is_fun then raise Not_found; (* TODO better error *)
          {a with a_op = Enode (Q q)}
      | Efun (ToQ f) ->
          let is_fun, q = qualify_var local_const f in
          if not is_fun then raise Not_found; (* TODO better error *)
          {a with a_op = Efun (Q q)}
      | _ -> a
    with Not_found -> a
  in
  a, local_const

let node_dec funs _ n =
  Idents.enter_node (current_qual n.n_name);
    (** Function to build the defined static parameters set [local_const].
        [local_const] associate to a name whether it is a fun instead of a var. *)
  let build_const loc p_list =
    let _add_const local_const p =
      if NamesEnv.mem p.p_name local_const
      then Hept_scoping.Error.message loc
             (Hept_scoping.Error.Econst_variable_already_defined p.p_name)
      else match p.p_type with
        | Ttype _ -> NamesEnv.add p.p_name false local_const
        | Tsig _ -> NamesEnv.add p.p_name true local_const
    in
    List.fold_left _add_const NamesEnv.empty p_list
  in
  let local_const = build_const n.n_loc n.n_params in
  let nd, _ = Hept_parsetree_mapfold.node_dec funs local_const n in
  let n_name = current_qual nd.n_name in
  (* /!\ we need to add the node to detect all the nodes,*)
  (* /!\ but we can't give their correct signature, scoping will correct this *)
  Hept_scoping.safe_add nd.n_loc add_value n_name Signature.dummy_node;
  nd, local_const

let const_dec funs local_const cd =
  let cd, _ = Hept_parsetree_mapfold.const_dec funs local_const cd in
  let c_name = current_qual cd.c_name in
  (* /!\ we need to add the consts to detect all the static_exps,*)
  (* /!\ but we can't qualify their types, scoping will correct this *)
  Hept_scoping.safe_add cd.c_loc add_const c_name (Signature.dummy_const Types.Tinvalid);
  cd, local_const

let program p =
  let funs = { Hept_parsetree_mapfold.defaults with
                node_dec = node_dec;
                exp = exp;
                app = app;
                static_exp = static_exp;
                const_dec = const_dec }
  in
  List.iter open_module p.p_opened;
  let p, _ = Hept_parsetree_mapfold.program_it funs Names.NamesEnv.empty p in
  p

let interface i =
  let funs = { Hept_parsetree_mapfold.defaults
               with node_dec = node_dec; exp = exp; const_dec = const_dec } in
  List.iter open_module i.i_opened;
  let i, _ = Hept_parsetree_mapfold.interface_it funs Names.NamesEnv.empty i in
  i

