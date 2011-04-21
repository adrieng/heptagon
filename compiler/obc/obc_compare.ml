open Obc
open Idents
open Global_compare
open Misc

let rec pat_compare pat1 pat2 =
  let cr = type_compare pat1.pat_ty pat2.pat_ty in
  if cr <> 0 then cr
  else
    match pat1.pat_desc, pat2.pat_desc with
      | Lvar x1, Lvar x2 -> ident_compare x1 x2
      | Lmem x1, Lmem x2 -> ident_compare x1 x2
      | Lfield(r1, f1), Lfield(r2, f2) ->
          let cr = compare f1 f2 in
            if cr <> 0 then cr else pat_compare r1 r2
      | Larray(l1, e1), Larray(l2, e2) ->
          let cr = pat_compare l1 l2 in
            if cr <> 0 then cr else exp_compare e1 e2
      | Lvar _, _ -> 1

      | Lmem _, Lvar _ -> -1
      | Lmem _, _ -> 1

      | Lfield _, (Lvar _ | Lmem _) -> -1
      | Lfield _, _ -> 1

      | Larray _, _ -> -1


and exp_compare e1 e2 =
  let cr = type_compare e1.e_ty e2.e_ty in
  if cr <> 0 then cr
  else
    match e1.e_desc, e2.e_desc with
      | Epattern pat1, Epattern pat2 -> pat_compare pat1 pat2
      | Econst se1, Econst se2 -> static_exp_compare se1 se2
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

      | Epattern _, _ -> 1

      | Econst _, Epattern _ -> -1
      | Econst _, _ -> 1

      | Eop _, (Epattern _ | Econst _) -> -1
      | Eop _, _ -> 1

      | Estruct _, (Epattern _ | Econst _ | Eop _) -> -1
      | Estruct _, _ -> 1

      | Earray _, _ -> -1
