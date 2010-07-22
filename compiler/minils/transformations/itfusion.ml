open Signature
open Modules
open Names
open Static
open Mls_mapfold
open Minils
(* Iterator fusion *)

let are_equal n m =
  let n = simplify NamesEnv.empty n in
  let m = simplify NamesEnv.empty m in
    n = m

let pat_of_vd_list l =
match l with
  | [vd] -> Evarpat (vd.v_ident)
  | _ -> Etuplepat (List.map (fun vd -> Evarpat vd.v_ident) l)

let tuple_of_vd_list l =
  let el = List.map (fun vd -> mk_exp ~exp_ty:vd.v_type (Evar vd.v_ident)) l in
  let ty = Types.prod (List.map (fun vd -> vd.v_type) l) in
    mk_exp ~exp_ty:ty (Eapp (mk_app Etuple, el, None))

let vd_of_arg ad =
  let n = match ad.a_name with None -> "_v" | Some n -> n in
    mk_var_dec (Ident.fresh n) ad.a_type

(** @return the lists of inputs and outputs (as var_dec) of
    an app object. *)
let get_node_inp_outp app = match app.a_op with
  | Enode f | Efun f ->
      let { info = ty_desc } = find_value f in
      let new_inp = List.map vd_of_arg ty_desc.node_outputs in
      let new_outp = List.map vd_of_arg ty_desc.node_outputs in
        new_inp, new_outp
  | Elambda(inp, outp, _,  _) ->
      inp, outp

(** Creates the equation to call the node [app].
    @return the list of new inputs required by the call, the expression
    used to retrieve the resul of the call and [acc_eq_list] with the
    added equations. *)
let mk_call app acc_eq_list =
  let new_inp, new_outp = get_node_inp_outp app in
  let args = List.map (fun vd -> mk_exp ~exp_ty:vd.v_type
                         (Evar vd.v_ident)) new_inp in
  let out_ty = Types.prod (List.map (fun vd -> vd.v_type) new_outp) in
  let e = mk_exp ~exp_ty:out_ty (Eapp (app, args, None)) in
  match List.length new_outp with
    | 1 -> new_inp, e, acc_eq_list
    | _ ->
        (*more than one output, we need to create a new equation *)
        let eq = mk_equation (pat_of_vd_list new_outp) e in
        let e = tuple_of_vd_list new_outp in
          new_inp, e, eq::acc_eq_list

let edesc funs acc ed =
  let ed, acc = Mls_mapfold.edesc funs acc ed in
  match ed with
    | Eiterator(Imap, f, n, e_list, r) ->
        (** @return the list of inputs of the anonymous function,
            a list of created equations (the body of the function),
            the args for the call of f in the lambda,
            the args for the iterator (ie the arrays).
            [b] is used to know whether some fusion can be done.

            map f (map g (x, y), z) --->
                   fun x', y', z' -> o1, o2 with
                        _v1, _v2 = g(x',y')
                        o1, o2 = f (_v1, _v2, z')
        *)
        let mk_arg e (inp, acc_eq_list, largs, args, b) = match e.e_desc with
          | Eiterator(Imap, g, m, local_args, _) when are_equal n m ->
              let new_inp, e, acc_eq_list = mk_call g acc_eq_list in
                new_inp @ inp, acc_eq_list, e::largs, local_args @ args, true
          | _ ->
              let vd = mk_var_dec (Ident.fresh "_x") e.e_ty in
              let x = mk_exp (Evar vd.v_ident) in
              vd::inp, acc_eq_list, x::largs, e::args, b
        in

        let inp, acc_eq_list, largs, args, can_be_fused =
          List.fold_right mk_arg e_list ([], [], [], [], false) in
          if can_be_fused then (
            (* create the call to f in the lambda fun *)
            let call = mk_exp (Eapp(f, largs, None)) in
            let _, outp = get_node_inp_outp f in
            let eq = mk_equation (pat_of_vd_list outp) call in
            (* create the lambda *)
            let lambda = mk_app (Elambda(inp, outp, [],
                                         eq::acc_eq_list)) in
              Eiterator(Imap, lambda, n, args, r), acc
          ) else
            ed, acc


    | _ -> raise Misc.Fallback


let program p =
  let funs = { Mls_mapfold.defaults with edesc = edesc } in
  let p, _ = Mls_mapfold.program_it funs false p in
    p
