
open Idents
open Minils


(**
  This module assumes that the memories are in the normal form :
    - all fby are either solo rhs or inside a when.
                - no tuple may be used to define a memory
*)



(** returns the set of var ident of the node [n] being memories *)
let memory_set n =
        let rec eq funs acc ({ eq_lhs = pat; eq_rhs = e } as equ) =
    match pat, e.e_desc with
    | _, Ewhen(e,_,_) ->
                          eq funs acc {equ with eq_rhs = e}
    | Evarpat x, Efby(_, _) ->
        equ, IdentSet.add x acc
    | _, _ -> equ, acc
  in
  let funs = { Mls_mapfold.defaults with Mls_mapfold.eq = eq } in
  let _, acc = Mls_mapfold.node_dec_it funs IdentSet.empty n in
  acc


let is_memory mem_set id =
        IdentSet.mem id mem_set


(** update the var_dec to ensure that the field v_is_memory is correct *)
let update_node n =
        let mems = memory_set n in
        let var_dec _ mems vd =
                { vd with v_is_memory = is_memory mems vd.v_ident  }, mems
  in
        let funs = { Mls_mapfold.defaults with Mls_mapfold.var_dec = var_dec } in
        let n, _ = Mls_mapfold.node_dec_it funs mems n in
        n
