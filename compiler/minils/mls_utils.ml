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
    | Econst se -> se
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
  let add x acc = if List.mem x acc then acc else x :: acc

  let rec vars_pat acc = function
    | Evarpat x -> x :: acc
    | Etuplepat pat_list -> List.fold_left vars_pat acc pat_list

  let rec vars_ck acc = function
    | Con(ck, c, n) -> add n acc
    | Cbase | Cvar { contents = Cindex _ } -> acc
    | Cvar { contents = Clink ck } -> vars_ck acc ck

  let read_exp read_funs (is_left, acc_init) e =
    (* recursive call *)
    let _,(_, acc) = Mls_mapfold.exp read_funs (is_left, acc_init) e in
    (* special cases *)
    let acc = match e.e_desc with
      | Evar x | Emerge(x,_) | Ewhen(_, _, x)
      | Eapp(_, _, Some x) | Eiterator (_, _, _, _, Some x) ->
          add x acc
      | Efby(_, e) ->
          if is_left then
            (* do not consider variables to the right
               of the fby, only clocks*)
            vars_ck acc_init e.e_ck
          else acc
      | _ -> acc
    in
    e, (is_left, vars_ck acc e.e_ck)

  let read_exp is_left acc e =
    let _, (_, acc) =
      Mls_mapfold.exp_it
        { Mls_mapfold.defaults with Mls_mapfold.exp = read_exp }
        (is_left, acc) e in
    acc

  let rec remove x = function
    | [] -> []
    | y :: l -> if x = y then l else y :: remove x l

  let def acc { eq_lhs = pat } = vars_pat acc pat

  let read is_left { eq_lhs = pat; eq_rhs = e } = match pat, e.e_desc with
    |  Evarpat(n), Efby(_, e1) ->
         if is_left
         then remove n (read_exp is_left [] e1)
         else read_exp is_left [] e1
    | _ -> read_exp is_left [] e

  let antidep { eq_rhs = e } =
    match e.e_desc with Efby _ -> true | _ -> false

  let clock { eq_rhs = e } = match e.e_desc with
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
  let memory_vars ({ eq_lhs = _; eq_rhs = e } as eq) = match e.e_desc with
    | Efby(_, _) -> def [] eq
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
