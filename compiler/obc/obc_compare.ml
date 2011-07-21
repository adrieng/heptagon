open Obc
open Idents
open Global_compare
open Misc

let rec extvalue_compare w1 w2 =
  let cr = type_compare w1.w_ty w2.w_ty in
  if cr <> 0 then cr
  else
    match w1.w_desc, w2.w_desc with
      | Wvar x1, Wvar x2 -> ident_compare x1 x2
      | Wmem x1, Wmem x2 -> ident_compare x1 x2
      | Wfield(r1, f1), Wfield(r2, f2) ->
          let cr = compare f1 f2 in
            if cr <> 0 then cr else extvalue_compare r1 r2
      | Warray(l1, e1), Warray(l2, e2) ->
          let cr = extvalue_compare l1 l2 in
            if cr <> 0 then cr else exp_compare e1 e2
      | Wvar _, _ -> 1

      | Wmem _, Wvar _ -> -1
      | Wmem _, _ -> 1

      | Wfield _, (Wvar _ | Wmem _) -> -1
      | Wfield _, _ -> 1

      | Wconst _, (Wvar _ | Wmem _ | Wfield _) -> -1
      | Wconst _, _ -> 1

      | Warray _, _ -> -1


and exp_compare e1 e2 =
  let cr = type_compare e1.e_ty e2.e_ty in
  if cr <> 0 then cr
  else
    match e1.e_desc, e2.e_desc with
      | Eextvalue w1, Eextvalue w2 -> extvalue_compare w1 w2
      | Eop(op1, el1), Eop(op2, el2) ->
          let cr = compare op1 op2 in
            if cr <> 0 then cr else list_compare exp_compare el1 el2
      | Estruct(_, fnel1), Estruct (_, fnel2) ->
          let compare_fne (fn1, e1) (fn2, e2) =
            let cr = compare fn1 fn2 in
              if cr <> 0 then cr else exp_compare e1 e2
          in
            list_compare compare_fne fnel1 fnel2
      | Earray el1, Earray el2 ->
          list_compare exp_compare el1 el2

      | Eextvalue _, _ -> 1

      | Eop _, (Eextvalue _) -> -1
      | Eop _, _ -> 1

      | Estruct _, (Eextvalue _ | Eop _) -> -1
      | Estruct _, _ -> 1

      | Earray _, _ -> -1


let rec compare_lhs_extvalue l w = match l.pat_desc, w.w_desc with
  | Lvar x1, Wvar x2 -> ident_compare x1 x2
  | Lmem x1, Wmem x2 -> ident_compare x1 x2
  | Lfield (l1, f1), Wfield (w2, f2) ->
    let cr = compare f1 f2 in
    if cr <> 0 then cr else compare_lhs_extvalue l1 w2
  | Larray (l1, e1), Warray (w2, e2) ->
    let cr = compare_lhs_extvalue l1 w2 in
    if cr <> 0 then cr else exp_compare e1 e2
  | _, _ -> 1 (* always return 1 as we only use it for comparison *)
