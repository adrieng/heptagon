(**************************************************************************)
(*                                                                        *)
(*  MiniLustre                                                            *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* clock checking *)

open Misc
open Ident
open Minils
open Signature
open Types
open Location
  
type error = | Etypeclash of ct * ct

exception TypingError of error
  
exception Unify
  
let error kind = raise (TypingError kind)
  
let message e kind =
  match kind with | Etypeclash (actual_ct, expected_ct) ->
	      Printf.eprintf "%aClock Clash: this expression has clock %a, \n\
                  but is expected to have clock %a.\n"
			    Mls_printer.print_exp e
				  Mls_printer.print_clock actual_ct
				  Mls_printer.print_clock expected_ct;
   raise Error
  
let index = ref 0
  
let gen_index () = (incr index; !index)
  
let new_var () = Cvar { contents = Cindex (gen_index ()); }

let rec repr ck =
  match ck with
  | Cbase | Con _ | Cvar { contents = Cindex _ } -> ck
  | Cvar (({ contents = Clink ck } as link)) ->
      let ck = repr ck in (link.contents <- Clink ck; ck)
  
let rec occur_check index ck =
  let ck = repr ck
  in
    match ck with
    | Cbase -> ()
    | Cvar { contents = Cindex n } when index <> n -> ()
    | Con (ck, _, _) -> occur_check index ck
    | _ -> raise Unify
  
let rec ck_value ck =
  match ck with
  | Cbase | Con _ | Cvar { contents = Cindex _ } -> ck
  | Cvar { contents = Clink ck } -> ck_value ck
  
let rec unify t1 t2 =
  if t1 == t2
  then ()
  else
    (match (t1, t2) with
     | (Ck ck1, Ck ck2) -> unify_ck ck1 ck2
     | (Cprod ct_list1, Cprod ct_list2) ->
         (try List.iter2 unify ct_list1 ct_list2 with | _ -> raise Unify)
     | _ -> raise Unify)

and unify_ck ck1 ck2 =
  let ck1 = repr ck1 in
  let ck2 = repr ck2
  in
    if ck1 == ck2
    then ()
    else
      (match (ck1, ck2) with
       | (Cbase, Cbase) -> ()
       | (Cvar { contents = Cindex n1 }, Cvar { contents = Cindex n2 }) when
           n1 = n2 -> ()
       | (Cvar (({ contents = Cindex n1 } as v)), _) ->
           (occur_check n1 ck2; v.contents <- Clink ck2)
       | (_, Cvar (({ contents = Cindex n2 } as v))) ->
           (occur_check n2 ck1; v.contents <- Clink ck1)
       | (Con (ck1, c1, n1), Con (ck2, c2, n2)) when (c1 = c2) & (n1 = n2) ->
           unify_ck ck1 ck2
       | _ -> raise Unify)
  
let rec eq ck1 ck2 =
  match ((repr ck1), (repr ck2)) with
  | (Cbase, Cbase) -> true
  | (Cvar { contents = Cindex n1 }, Cvar { contents = Cindex n2 }) -> true
  | (Con (ck1, _, n1), Con (ck2, _, n2)) when n1 = n2 -> eq ck1 ck2
  | _ -> false
  
let rec unify t1 t2 =
  match (t1, t2) with
  | (Ck ck1, Ck ck2) -> unify_ck ck1 ck2
  | (Cprod t1_list, Cprod t2_list) -> unify_list t1_list t2_list
  | _ -> raise Unify

and unify_list t1_list t2_list =
  try List.iter2 unify t1_list t2_list with | _ -> raise Unify
  
let rec skeleton ck = function
  | Tprod ty_list -> Cprod (List.map (skeleton ck) ty_list)
  | Tarray _ | Tid _ -> Ck ck
  
let ckofct = function | Ck ck -> repr ck | Cprod ct_list -> Cbase
  
let prod =
  function | [] -> assert false | [ ty ] -> ty | ty_list -> Tprod ty_list
  
let typ_of_name h x = Env.find x h
  
let rec typing h e =
  let ct =
    match e.e_desc with
    | Econst _ | Econstvar _ -> Ck (new_var ())
    | Evar x -> Ck (typ_of_name h x)
    | Efby (c, e) -> typing h e
    | Etuple e_list -> Cprod (List.map (typing h) e_list)
    | Ecall(_, e_list, r) ->
        let ck_r = match r with
                   | None -> new_var()
                   | Some(reset) -> typ_of_name h reset
        in (List.iter (expect h (Ck ck_r)) e_list; skeleton ck_r e.e_ty)
    | Ecall(_, e_list, Some(reset)) ->
        let ck_r = typ_of_name h reset
        in (List.iter (expect h (Ck ck_r)) e_list; skeleton ck_r e.e_ty)
    | Ewhen (e, c, n) ->
        let ck_n = typ_of_name h n
        in (expect h (skeleton ck_n e.e_ty) e;
            skeleton (Con (ck_n, c, n)) e.e_ty)
    | Eifthenelse (e1, e2, e3) ->
        let ck = new_var () in
        let ct = skeleton ck e.e_ty
        in (expect h (Ck ck) e1; expect h ct e2; expect h ct e3; ct)
    | Emerge (n, c_e_list) ->
        let ck_c = typ_of_name h n
        in (typing_c_e_list h ck_c n c_e_list; skeleton ck_c e.e_ty)
    | Efield (e1, n) ->
        let ck = new_var () in
        let ct = skeleton ck e1.e_ty in (expect h (Ck ck) e1; ct)
    | Efield_update (_, e1, e2) ->
        let ck = new_var () in
        let ct = skeleton ck e.e_ty
        in (expect h (Ck ck) e1; expect h ct e2; ct)
    | Estruct l ->
        let ck = new_var () in
	      (List.iter
	         (fun (n, e) -> let ct = skeleton ck e.e_ty in expect h ct e) l;
	       Ck ck)
    | Earray e_list ->
        let ck = new_var ()
        in (List.iter (expect h (Ck ck)) e_list; skeleton ck e.e_ty)
    | Earray_op(op) -> typing_array_op h e op
  in (e.e_ck <- ckofct ct; ct)

and typing_array_op h e = function
    | Erepeat (_, e) -> typing h e
    | Eselect (_, e) -> typing h e
    | Eselect_dyn (e_list, _, e, defe) ->
        let ck = new_var () in
        let ct = skeleton ck e.e_ty
        in (expect h ct e; List.iter (expect h ct) e_list; ct)
    | Eupdate (_, e1, e2) ->
        let ck = new_var () in
        let ct = skeleton ck e.e_ty
        in (expect h (Ck ck) e1; expect h ct e2; ct)
    | Eselect_slice (_, _, e) -> typing h e
    | Econcat (e1, e2) ->
        let ck = new_var () in
        let ct = skeleton ck e.e_ty
        in (expect h (Ck ck) e1; expect h ct e2; ct)
    | Eiterator (_, _, _, e_list, r) ->
        let ck_r = match r with
                   | None -> new_var()
                   | Some(reset) -> typ_of_name h reset
        in (List.iter (expect h (Ck ck_r)) e_list; skeleton ck_r e.e_ty)


and expect h expected_ty e =
  let actual_ty = typing h e
  in
    try unify actual_ty expected_ty
    with | Unify -> message e (Etypeclash (actual_ty, expected_ty))

and typing_c_e_list h ck_c n c_e_list =
  let rec typrec =
    function
    | [] -> ()
    | (c, e) :: c_e_list ->
        (expect h (skeleton (Con (ck_c, c, n)) e.e_ty) e; typrec c_e_list)
  in typrec c_e_list
  
let rec typing_pat h =
  function
  | Evarpat x -> Ck (typ_of_name h x)
  | Etuplepat pat_list -> Cprod (List.map (typing_pat h) pat_list)
  
let typing_eqs h eq_list =
  List.iter
    (fun { eq_lhs = pat; eq_rhs = e } ->
       match e.e_desc with (*TODO FIXME*)
       | _ ->
           let ty_pat = typing_pat h pat
           in
             (try expect h ty_pat e
              with
              | Error ->
                  (* TODO remettre en route quand Printer fonctionne

        (* DEBUG *)
		  Printf.eprintf "Complete expression: %a\n"
		    Printer.print_exp e;
		  Printf.eprintf "Clock pattern: %a\n"
		    Printer.print_clock ty_pat; *)
                  raise Error))
    eq_list
  
let build h dec =
  List.fold_left (fun h { v_name = n } -> Env.add n (new_var ()) h) h dec
  
let sbuild h dec base =
  List.fold_left (fun h { v_name = n } -> Env.add n base h) h dec
  
let typing_contract h contract base =
  match contract with
  | None -> h
  | Some
      {
        c_local = l_list;
        c_eq = eq_list;
        c_assume = e_a;
        c_enforce = e_g;
        c_controllables = c_list
      } ->
      let h = sbuild h c_list base in
      let h' = build h l_list
      in
        (* assumption *)
        (* property *)
        (typing_eqs h' eq_list;
         expect h' (Ck base) e_a;
         expect h' (Ck base) e_g;
         h)
  
let typing_node (({
                    n_name = f;
                    n_input = i_list;
                    n_output = o_list;
                    n_contract = contract;
                    n_local = l_list;
                    n_equs = eq_list
                  } as node))
                =
  let base = Cbase in
  let h = sbuild Env.empty i_list base in
  let h = sbuild h o_list base in
  let h = typing_contract h contract base in
  let h = build h l_list
  in
    (typing_eqs h eq_list;
     (*update clock info in variables descriptions *)
     let set_clock vd =
       { (vd) with v_clock = ck_value (Env.find vd.v_name h); }
     in
       {
         (node)
         with
         n_input = List.map set_clock i_list;
         n_output = List.map set_clock o_list;
         n_local = List.map set_clock l_list;
       })
  
let program (({ p_nodes = p_node_list } as p)) =
  { (p) with p_nodes = List.map typing_node p_node_list; }
  
