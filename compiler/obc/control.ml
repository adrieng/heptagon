(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* control optimisation *)

(* TODO could optimize for loops ? *)

open Idents
open Misc
open Obc
open Obc_utils
open Clocks
open Signature
open Obc_mapfold

let appears_in_exp, appears_in_lhs =
  let lhsdesc _ (x, acc) ld = match ld with
    | Lvar y -> ld, (x, acc or (x=y))
    | Lmem y -> ld, (x, acc or (x=y))
    | _ -> raise Errors.Fallback
  in
  let funs = { Obc_mapfold.defaults with lhsdesc = lhsdesc } in
  let appears_in_exp x e =
    let _, (_, acc) = exp_it funs (x, false) e in
      acc
    in
  let appears_in_lhs x l =
    let _, (_, acc) = lhs_it funs (x, false) l in
      acc
  in
    appears_in_exp, appears_in_lhs

let used_vars e =
  let add x acc = if List.mem x acc then acc else x::acc in
  let lhsdesc funs acc ld = match ld with
    | Lvar y -> ld, add y acc
    | Lmem y -> ld, add y acc
    | _ -> raise Errors.Fallback
  in
  let funs = { Obc_mapfold.defaults with lhsdesc = lhsdesc } in
  let _, vars = Obc_mapfold.exp_it funs [] e in
    vars

let rec is_modified_by_call x args e_list = match args, e_list with
  | [], [] -> false
  | a::args, e::e_list ->
    if Linearity.is_linear a.a_linearity && appears_in_exp x e then
      true
    else
      is_modified_by_call x args e_list
  | _, _ -> assert false

let is_modified_handlers j x handlers =
  let act _ acc a = match a with
    | Aassgn(l, _) -> a, acc or (appears_in_lhs x l)
    | Acall_fun(name_list, f, e_list) ->
        (* first, check if e is one of the output of the function*)
        if List.exists (appears_in_lhs x) name_list then
          a, true
        else (
          let sig_info = Modules.find_value f in
            a, acc or (is_modified_by_call x sig_info.node_inputs e_list)
        )
    | Acall (name_list, o, Mstep, e_list) ->
        (* first, check if e is one of the output of the function*)
        if List.exists (appears_in_lhs x) name_list then
          a, true
        else (
          let sig_info = find_obj (obj_ref_name o) j in
            a, acc or (is_modified_by_call x sig_info.node_inputs e_list)
        )
    | _ -> raise Errors.Fallback
  in
  let funs = { Obc_mapfold.defaults with act = act } in
    List.exists (fun (_, b) -> snd (block_it funs false b)) handlers

let is_modified_handlers j e handlers =
  let vars = used_vars e in
    List.exists (fun x -> is_modified_handlers j x handlers) vars

let fuse_blocks b1 b2 =
  { b_locals = b1.b_locals @ b2.b_locals;
      b_body = b1.b_body @ b2.b_body }

let rec find c = function
  | []    -> raise Not_found
  | (c1, s1) :: h  ->
      if c = c1 then s1, h else let s, h = find c h in s, (c1, s1) :: h

let is_deadcode = function (* TODO Etrange puisque c'est apres la passe de deadcode ? *)
    | Aassgn (lhs, e) ->
        (match e.e_desc with
           | Eextvalue w -> Obc_compare.compare_lhs_extvalue lhs w = 0
           | _ -> false
        )
    | Acase (_, []) -> true
    | Afor(_, _, _, { b_body = [] }) -> true
    | _ -> false

let rec joinlist j l =
  let rec join_next l =
    match l with
      | [] -> []
      | [s1] -> [s1]
      | s1::s2::l ->
          match s1, s2 with
            | Acase(e1, h1),
              Acase(e2, h2) when Obc_compare.exp_compare e1 e2 = 0 ->
                let fused_switch = Acase(e1, joinhandlers j h1 h2) in
                if is_modified_handlers j e2 h1 then
                  fused_switch::(join_first l)
                else
                  join_next (fused_switch::l)
            | s1, s2 -> s1::(join_first (s2::l))
  and join_first l =
    match l with
      | [] -> []
      | (Acase(e1, h1))::l ->
          if is_modified_handlers j e1 h1 then
            (Acase(e1, h1))::(join_next l)
          else
            join_next ((Acase(e1, h1))::l)
      | _ -> join_next l
  in
    join_first l


and join_block j b =
  { b with b_body = joinlist j b.b_body }

and joinhandlers j h1 h2 =
  match h1 with
    | [] -> h2
    | (c1, s1) :: h1' ->
        let s1', h2' =
          try let s2, h2'' = find c1 h2 in fuse_blocks s1 s2, h2''
          with Not_found -> s1, h2 in
        (c1, join_block j s1') :: joinhandlers j h1' h2'

let block funs j b =
  let b, _ = Obc_mapfold.block funs j b in
  { b with b_body = joinlist j b.b_body }, j

let class_def funs acc cd =
  let cd, _ = Obc_mapfold.class_def funs cd.cd_objs cd in
    cd, acc

let program p =
  let p, _ = program_it { defaults with class_def = class_def; block = block } [] p in
  p
