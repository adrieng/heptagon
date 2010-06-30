open Minils
open Mls_printer
open Location
open Names
open Ident
open Signature
open Static
open Types
open Misc

(** Error Kind *)
type err_kind = | Enot_static_exp

let err_message ?(exp=void) ?(loc=exp.e_loc) = function
  | Enot_static_exp ->
      Printf.eprintf "The expression %a should be a static_exp.@."
        print_exp exp;
      raise Error

let rec static_exp_of_exp e =
  match e.e_desc with
    | Econstvar n -> Svar n
    | Econst (Cint i) -> Sconst i
    | Ecall(op, [e1;e2], _) ->
        let sop = op_from_app_name op.op_name in
        Sop(sop, static_exp_of_exp e1, static_exp_of_exp e2)
    | _ -> err_message ~exp:e Enot_static_exp

(** @return the list of bounds of an array type*)
let rec bounds_list ty =
  match ty with
    | Tarray(ty, n) -> n::(bounds_list ty)
    | _ -> []

(** @return the [var_dec] object corresponding to the name [n]
    in a list of [var_dec]. *)
let rec vd_find n = function
  | [] -> Format.printf "Not found var %s\n" (name n); raise Not_found
  | vd::l ->
      if vd.v_ident = n then vd else vd_find n l

(** @return whether an object of name [n] belongs to
    a list of [var_dec]. *)
let rec vd_mem n = function
  | [] -> false
  | vd::l -> vd.v_ident = n or (vd_mem n l)

(** @return whether [ty] corresponds to a record type. *)
let is_record_type ty = match ty with
  | Tid n ->
      (try
         ignore (Modules.find_struct n); true
       with
           Not_found -> false)
  | _ -> false

let is_op = function
  | Modname { qual = "Pervasives"; id = _ } -> true | _ -> false

module Vars =
struct
  let add x acc =
    if List.mem x acc then acc else x :: acc

  let rec vars_pat acc = function
    | Evarpat x -> x :: acc
    | Etuplepat pat_list -> List.fold_left vars_pat acc pat_list

  let rec vars_ck acc = function
    | Con(ck, c, n) -> add n acc
    | Cbase | Cvar { contents = Cindex _ } -> acc
    | Cvar { contents = Clink ck } -> vars_ck acc ck

  let rec read is_left acc e =
    let acc =
      match e.e_desc with
        | Evar n -> add n acc
        | Emerge(x, c_e_list) ->
            let acc = add x acc in
            List.fold_left (fun acc (_, e) -> read is_left acc e) acc c_e_list
        | Eifthenelse(e1, e2, e3) ->
            read is_left (read is_left (read is_left acc e1) e2) e3
        | Ewhen(e, c, x) ->
            let acc = add x acc in
            read is_left acc e
        | Etuple(e_list) -> List.fold_left (read is_left) acc e_list
        | Ecall(_, e_list, None) ->
            List.fold_left (read is_left) acc e_list
        | Ecall(_, e_list, Some x) ->
            let acc = add x acc in
            List.fold_left (read is_left) acc e_list
        | Efby(_, e) ->
            if is_left then vars_ck acc e.e_ck else read is_left acc e
        | Efield(e, _) -> read is_left acc e
        | Estruct(f_e_list) ->
            List.fold_left (fun acc (_, e) -> read is_left acc e) acc f_e_list
        | Econst _ | Econstvar _ -> acc
        | Efield_update (_, e1, e2) ->
            read is_left (read is_left acc e1) e2
              (*Array operators*)
        | Earray e_list -> List.fold_left (read is_left) acc e_list
        | Earray_op op -> read_array_op is_left acc op
    in
    vars_ck acc e.e_ck

  and read_array_op is_left acc = function
    | Erepeat (_,e) -> read is_left acc e
    | Eselect (_,e) -> read is_left acc e
    | Eselect_dyn (e_list, e1, e2) ->
        let acc = List.fold_left (read is_left) acc e_list in
        read is_left (read is_left acc e1) e2
    | Eupdate (_, e1, e2) ->
        read is_left (read is_left acc e1) e2
    | Eselect_slice (_ , _, e) -> read is_left acc e
    | Econcat (e1, e2) ->
        read is_left (read is_left acc e1) e2
    | Eiterator (_, _, _, e_list, None) ->
        List.fold_left (read is_left) acc e_list
    | Eiterator (_, _, _, e_list, Some x) ->
        let acc = add x acc in
        List.fold_left (read is_left) acc e_list

  let rec remove x = function
    | [] -> []
    | y :: l -> if x = y then l else y :: remove x l

  let def acc { eq_lhs = pat } = vars_pat acc pat

  let read is_left { eq_lhs = pat; eq_rhs = e } =
    match pat, e.e_desc with
      |  Evarpat(n), Efby(_, e1) ->
           if is_left
           then remove n (read is_left [] e1)
           else read is_left [] e1
      | _ -> read is_left [] e

  let antidep { eq_rhs = e } =
    match e.e_desc with Efby _ -> true | _ -> false

  let clock { eq_rhs = e } =
    match e.e_desc with
      | Emerge(_, (_, e) :: _) -> e.e_ck
      | _ -> e.e_ck

  let head ck =
    let rec headrec ck l =
      match ck with
        | Cbase | Cvar { contents = Cindex _ } -> l
        | Con(ck, c, n) -> headrec ck (n :: l)
        | Cvar { contents = Clink ck } -> headrec ck l
    in
    headrec ck []

  (** Returns a list of memory vars (x in x = v fby e)
      appearing in an equation. *)
  let memory_vars ({ eq_lhs = _; eq_rhs = e } as eq)  =
    match e.e_desc with
      |  Efby(_, _) -> def [] eq
      | _ -> []
end


(* data-flow dependences. pre-dependences are discarded *)
module DataFlowDep = Dep.Make
  (struct
     type equation = eq
     let read eq = Vars.read true eq
     let def = Vars.def
     let antidep = Vars.antidep
   end)

(* all dependences between variables *)
module AllDep = Dep.Make
  (struct
     type equation = eq
     let read eq = Vars.read false eq
     let def = Vars.def
     let antidep eq = false
   end)
