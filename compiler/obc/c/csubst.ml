open C
open Idents
open Names

let rec subst_stm map stm = match stm with
  | Csexpr e -> Csexpr (subst_exp map e)
  | Cskip -> Cskip
  | Creturn e -> Creturn (subst_exp map e)
  | Csblock cblock ->
      Csblock (subst_block map cblock)
  | Caffect (lhs, e) ->
      Caffect(subst_lhs map lhs, subst_exp map e)
  | Cif (e, truel, falsel) ->
      Cif (subst_exp map e, subst_stm_list map truel,
           subst_stm_list map falsel)
  | Cswitch (e, l) ->
      Cswitch (subst_exp map e
                 , List.map (fun (s, sl) -> s, subst_stm_list map sl) l)
  | Cwhile (e, l) ->
      Cwhile (subst_exp map e, subst_stm_list map l)
  | Cfor (x, i1, i2, l) ->
      Cfor (x, i1, i2, subst_stm_list map l)

and subst_stm_list map =
  List.map (subst_stm map)

and subst_lhs map lhs =
  match lhs with
    | Cvar n ->
        if NamesEnv.mem n map then NamesEnv.find n map else lhs
    | Cfield (lhs, s) -> Cfield (subst_lhs map lhs, s)
    | Carray (lhs, n) -> Carray (subst_lhs map lhs, subst_exp map n)
    | Cderef lhs -> Cderef (subst_lhs map lhs)

and subst_exp map = function
  | Cuop (op, e) -> Cuop (op, subst_exp map e)
  | Cbop (s, l, r) -> Cbop (s, subst_exp map l, subst_exp map r)
  | Cfun_call (s, el) -> Cfun_call (s, subst_exp_list map el)
  | Cconst x -> Cconst x
  | Clhs lhs -> Clhs (subst_lhs map lhs)
  | Caddrof lhs -> Caddrof (subst_lhs map lhs)
  | Cstructlit (s, el) -> Cstructlit (s, subst_exp_list map el)
  | Carraylit el ->  Carraylit (subst_exp_list map el)

and subst_exp_list map =
  List.map (subst_exp map)

and subst_block map b =
  { b with block_body = subst_stm_list map b.block_body }

let assoc_map_for_fun md =
  match md.Obc.m_outputs with
    | [] -> NamesEnv.empty
    | out ->
        let fill_field map vd =
          NamesEnv.add (name vd.Obc.v_ident)
            (Cfield (Cderef (Cvar "out"), local_qn (name vd.Obc.v_ident))) map
        in
        List.fold_left fill_field NamesEnv.empty out

