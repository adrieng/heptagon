open Obc
open Obc_mapfold

let is_deadcode = function
    | Aassgn (lhs, e) ->
        (match e.e_desc with
           | Eextvalue w -> Obc_compare.compare_lhs_extvalue lhs w = 0
           | _ -> false
        )
    | Acase (_, []) -> true
    | Afor(_, _, _, { b_body = [] }) -> true
    | _ -> false

let act funs act_list a =
  let a, _ = Obc_mapfold.act funs [] a in
    if is_deadcode a then
      a, act_list
    else
      a, a::act_list

let block funs acc b =
  let _, act_list = Obc_mapfold.block funs [] b in
    { b with b_body = List.rev act_list }, acc

let program p =
  let funs = { Obc_mapfold.defaults with block = block; act = act } in
  let p, _ = Obc_mapfold.program_it funs [] p in
    p

