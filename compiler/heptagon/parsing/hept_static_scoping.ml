open Modules
open Hept_parsetree
open Hept_parsetree_mapfold
open Hept_scoping

(* Convert expressions that should be static to the corresponding
   static expression. After this pass, all the static expressions
   (including variables) are of type Econst se. *)

exception Not_static

let assert_se e = match e.e_desc with
  | Econst se -> se
  | _ -> raise Not_static

let static_exp funs local_const se =
  (match se.se_desc with
    | Svar (Q q) ->
        if not (Modules.check_const q) then
          Error.message se.se_loc (Error.Equal_notfound("constant", q))
    | _ -> ());
  Hept_parsetree_mapfold.static_exp funs local_const se

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
              (try Svar (Q (qualify_const local_const (ToQ n)))
              with Error.ScopingError _ -> raise Not_static)
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
          | _ -> raise Not_static
      in
      { e with e_desc = Econst (mk_static_exp sed e.e_loc) }, local_const
    with
        Not_static -> e, local_const

let node funs _ n =
  let local_const = Hept_scoping.build_const n.n_loc n.n_params in
  Hept_parsetree_mapfold.node_dec funs local_const n

let const_dec funs local_const cd =
  let cd, _ = Hept_parsetree_mapfold.const_dec funs local_const cd in
  let c_name = current_qual cd.c_name in
  (* /!\ we need to add the consts to detect all the static_exps,*)
  (* /!\ but we can't qualify their types, scoping will correct this *)
  add_const c_name (Signature.mk_const_def Types.Tinvalid (Initial.mk_static_string "invalid"));
  cd, local_const

let interface_desc _ local_const id = match id with
  | Iopen n -> open_module n; id, local_const
  | _ -> raise Errors.Fallback

let program p =
  let funs = { Hept_parsetree_mapfold.defaults
               with node_dec = node; exp = exp; static_exp = static_exp; const_dec = const_dec } in
  List.iter open_module p.p_opened;
  let p, _ = Hept_parsetree_mapfold.program_it funs Names.NamesSet.empty p in
  p

let interface i =
  let funs = { Hept_parsetree_mapfold.defaults
               with node_dec = node; exp = exp; const_dec = const_dec } in
  let i, _ = Hept_parsetree_mapfold.interface_it funs Names.NamesSet.empty i in
  i

