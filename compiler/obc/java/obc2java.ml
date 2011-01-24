(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(** An Obc.program is a Java.package,
       Obc.type_dec, Obc.class_def are Java.classs
       Obc.const_dec is defined in the special class CONSTANTES
       Obc.Lvar are Pvar
       Obc.Lmem are this.Pvar (Pfield)
       Obc.Oobj and Oarray are simply Pvar and Parray_elem
       Obc.Types_alias are dereferenced since no simple type alias is possible in Java *)

open Format
open Misc
open Names
open Modules
open Signature
open Obc
open Java


let fresh_it () =
  let id = Idents.gen_var "obc2java" "i" in
  id, mk_var_dec id Tint

(** fresh Afor from 0 to [size] with [body] a function from [var_ident] (the iterator) to [act] list *)
let fresh_for size body =
  let i, id = fresh_it () in
  Afor (id, Sint 0, size, mk_block (body i))


(** a [Module] becomes a [package] *)
let translate_qualname q = match q with
  | { qual = "Pervasives" } -> q
  | { qual = m } when m = g_env.current_mod -> q (* current module is not translated to keep track,
                                                    there is no issue since printed without the qualifier *)
  | { qual = m } when m = local_qualname -> q
  | _ -> { q with qual = String.lowercase q.qual }

(** a [Module.const] becomes a [module.CONSTANTES.CONST] *)
let translate_const_name q = match q with
  | { qual = m } when m = local_qualname -> { q with name = String.uppercase q.name }
  | _ -> { q with qual = (String.lowercase q.qual)^ ".CONSTANTES"; name = String.uppercase q.name }

(** a [Module.name] becomes a [module.Name]
    used for type_names, class_names, fun_names *)
let qualname_to_class_name q =
  let q = translate_qualname q in
  { q with name = String.capitalize q.name }

(** a [Module.Constr] of an [Module.enum] type becomes a [module.Enum.CONSTR] of the [module.Enum] class *)
let _translate_constructor_name q q_ty = (* TODO java recursive qualname ! *)
  let classe = qualname_to_class_name q_ty in
  let q = qualname_to_class_name q in
  { q with name = classe.name ^ "." ^ q.name }

let translate_constructor_name q =
  match Modules.find_constrs q with
    | Types.Tid q_ty when q_ty = Initial.pbool -> q |> shortname |> local_qn
    | Types.Tid q_ty -> _translate_constructor_name q q_ty
    | _ -> assert false

let translate_field_name f = f |> Names.shortname |> String.lowercase

(** a [name] becomes a [package.Name] *)
let name_to_classe_name n = n |> Modules.current_qual |> qualname_to_class_name

(** translate an ostatic_exp into an jexp *)
let rec static_exp param_env se = match se.Types.se_desc with
  | Types.Svar c ->
      if shortname c = local_qualname
      then let n = NamesEnv.find (shortname c) param_env in Svar (n |> Idents.name |> local_qn)
      else Svar (translate_const_name c)
  | Types.Sint i -> Sint i
  | Types.Sfloat f -> Sfloat f
  | Types.Sbool b -> Sbool b
  | Types.Sconstructor c -> let c = translate_constructor_name c in Sconstructor c
  | Types.Sfield f -> eprintf "ojSfield @."; assert false;
  | Types.Stuple t -> eprintf "ojStuple@."; assert false;
  (* TODO java ?? not too difficult if needed, return Tuplen<..>() *)
  | Types.Sarray_power _ -> eprintf "ojSarray_power@."; assert false; (* TODO java array *)
  | Types.Sarray se_l -> Enew_array (ty param_env se.Types.se_ty, List.map (static_exp param_env) se_l)
  | Types.Srecord _ -> eprintf "ojSrecord@."; assert false; (* TODO java *)
  | Types.Sop (f, se_l) -> Efun (qualname_to_class_name f, List.map (static_exp param_env) se_l)

and boxed_ty param_env t = match t with
  | Types.Tprod ty_l ->
      let ln = ty_l |> List.length |> Pervasives.string_of_int in
      Tgeneric ({ qual = "heptagon"; name = "Tuple"^ln }, List.map (boxed_ty param_env) ty_l)
  | Types.Tid t when t = Initial.pbool -> Tclass (Names.local_qn "Boolean")
  | Types.Tid t when t = Initial.pint -> Tclass (Names.local_qn "Integer")
  | Types.Tid t when t = Initial.pfloat -> Tclass (Names.local_qn "Float")
  | Types.Tid t -> Tclass (qualname_to_class_name t)
  | Types.Tarray (t,size) -> Tarray (boxed_ty param_env t, static_exp param_env size)
  | Types.Tasync _ -> assert false; (* TODO async *)
  | Types.Tunit -> Tunit

and ty param_env t :Java.ty = match t with
  | Types.Tprod ty_l ->
      let ln = ty_l |> List.length |> Pervasives.string_of_int in
      Tgeneric ({ qual = "heptagon"; name = "Tuple"^ln }, List.map (boxed_ty param_env) ty_l)
  | Types.Tid t when t = Initial.pbool -> Tbool
  | Types.Tid t when t = Initial.pint -> Tint
  | Types.Tid t when t = Initial.pfloat -> Tfloat
  | Types.Tid t -> Tclass (qualname_to_class_name t)
  | Types.Tarray (t,size) -> Tarray (ty param_env t, static_exp param_env size)
  | Types.Tasync _ -> assert false; (* TODO async *)
  | Types.Tunit -> Tunit

let var_dec param_env vd = { vd_type = ty param_env vd.v_type; vd_ident = vd.v_ident }

let var_dec_list param_env vd_l = List.map (var_dec param_env) vd_l

let rec exp param_env e = match e.e_desc with
  | Obc.Epattern p -> Eval (pattern param_env p)
  | Obc.Econst se -> static_exp param_env se
  | Obc.Eop (op,e_l) -> Efun (op, exp_list param_env e_l)
  | Obc.Estruct _ -> eprintf "ojEstruct@."; assert false (* TODO java *)
  | Obc.Earray e_l -> Enew_array (ty param_env e.e_ty, exp_list param_env e_l)
  | Obc.Ebang _ -> eprintf "ojEbang@."; assert false (* TODO java async *)

and exp_list param_env e_l = List.map (exp param_env) e_l

and pattern param_env p = match p.pat_desc with
  | Obc.Lvar v -> Pvar v
  | Obc.Lmem v -> Pthis v
  | Obc.Lfield (p,f) -> Pfield (pattern param_env p, translate_field_name f)
  | Obc.Larray (p,e) -> Parray_elem (pattern param_env p, exp param_env e)

let obj_ref param_env o = match o with
  | Oobj id -> Pvar id
  | Oarray (id,p) -> Parray_elem (Pvar id, Eval (pattern param_env p))

let rec act_list param_env act_l acts =
  let _act act acts = match act with
    | Obc.Aassgn (p,e) -> (Aassgn (pattern param_env p, exp param_env e))::acts
    | Obc.Acall ([], obj, Mstep, e_l) ->
        let acall = Amethod_call (obj_ref param_env obj, "step", exp_list param_env e_l) in
        acall::acts
    | Obc.Acall ([p], obj, Mstep, e_l) ->
        let ecall = Emethod_call (obj_ref param_env obj, "step", exp_list param_env e_l) in
        let assgn = Aassgn (pattern param_env p, ecall) in
        assgn::acts
    | Obc.Acall (p_l, obj, Mstep, e_l) ->
        let return_ty = p_l |> pattern_list_to_type |> (ty param_env) in
        let return_id = Idents.gen_var "obc2java" "out" in
        let return_vd = { vd_type = return_ty; vd_ident = return_id } in
        let ecall = Emethod_call (obj_ref param_env obj, "step", exp_list param_env e_l) in
        let assgn = Anewvar (return_vd, ecall) in
        let copy_return_to_var i p =
          Aassgn (pattern param_env p, Eval (Pfield (Pvar return_id, "c"^(string_of_int i))))
        in
        let copies = Misc.mapi copy_return_to_var p_l in
        assgn::(copies@acts)
    | Obc.Acall (_, obj, Mreset, _) ->
        let acall = Amethod_call (obj_ref param_env obj, "reset", []) in
        acall::acts
    | Obc.Aasync_call _ -> assert false (* TODO java async *)
    | Obc.Acase (e, c_b_l) when e.e_ty = Types.Tid Initial.pbool ->
        (match c_b_l with
          | [] -> acts
          | [(c,b)] when c = Initial.ptrue ->
              (Aif (exp param_env e, block param_env b)):: acts
          | [(c,b)] when c = Initial.pfalse ->
              (Aifelse (exp param_env e, {b_locals = []; b_body = []}, block param_env b)) :: acts
          | _ ->
              let _, _then = List.find (fun (c,b) -> c = Initial.ptrue) c_b_l in
              let _, _else = List.find (fun (c,b) -> c = Initial.pfalse) c_b_l in
              (Aifelse (exp param_env e, block param_env _then, block param_env _else)) :: acts)
    | Obc.Acase (e, c_b_l) ->
        let _c_b (c,b) = translate_constructor_name c, block param_env b in
        let acase = Aswitch (exp param_env e, List.map _c_b c_b_l) in
        acase::acts
    | Obc.Afor (v, se, se', b) ->
        let afor = Afor (var_dec param_env v, static_exp param_env se, static_exp param_env se', block param_env b) in
        afor::acts
  in
  List.fold_right _act act_l acts

and block param_env ?(locals=[]) ?(end_acts=[]) ob =
  let blocals = var_dec_list param_env ob.Obc.b_locals in
  let locals = locals @ blocals in
  let acts = act_list param_env ob.Obc.b_body end_acts in
  { b_locals = locals; b_body = acts }

let class_def_list classes cd_l =
  let class_def classes cd =
    Idents.enter_node cd.cd_name;
    let class_name = qualname_to_class_name cd.cd_name in
     (* [param_env] is an env mapping local param name to ident *)
    let constructeur, param_env =
      let param_to_arg param_env p =
        let p_ident = Idents.gen_var "obc2java" (String.uppercase p.Signature.p_name) in
        let p_vd = { vd_ident = p_ident; vd_type = ty param_env p.Signature.p_type } in
        let param_env = NamesEnv.add p.Signature.p_name p_ident param_env in
        p_vd, param_env
      in
      let args, param_env = Misc.mapfold param_to_arg NamesEnv.empty cd.cd_params in
      let body =
        (* TODO java array : also initialize arrays with [ new int[3] ] *)
        let final_field_init_act arg = Aassgn (Pthis arg.vd_ident, Eval (Pvar arg.vd_ident)) in
        let obj_init_act acts od =
          let params = List.map (static_exp param_env) od.o_params in
          let act = match od.o_size with
            | None -> [ Aassgn (Pthis od.o_ident, Enew (Tclass od.o_class, params)) ]
            | Some size ->
                let size = static_exp param_env size in
                let assgn_elem i =
                  [ Aassgn (Parray_elem (Pthis od.o_ident, mk_var i), Enew (Tclass od.o_class, params)) ]
                in
                [ Aassgn (Pthis od.o_ident, Enew (Tarray (Tclass od.o_class,size), []));
                  fresh_for size assgn_elem ]
          in
          act@acts
        in
        let acts = List.map final_field_init_act args in
        let acts = List.fold_left obj_init_act acts cd.cd_objs in
        { b_locals = []; b_body = acts }
      in
      mk_methode ~args:args body (shortname class_name), param_env
    in
    let fields =
      let mem_to_field fields vd = (mk_field ~protection:Pprotected (ty param_env vd.v_type) vd.v_ident) :: fields in
      let obj_to_field fields od =
        let jty = match od.o_size with
          | None -> Tclass (qualname_to_class_name od.o_class)
          | Some size -> Tarray (Tclass (qualname_to_class_name od.o_class), static_exp param_env size)
        in
        (mk_field ~protection:Pprotected jty od.o_ident) :: fields
      in
      let params_to_field fields p =
        let p_ident = NamesEnv.find p.p_name param_env in
        (mk_field ~protection:Pprotected ~final:true (ty param_env p.p_type) p_ident) :: fields
      in
      let fields = List.fold_left mem_to_field [] cd.cd_mems in
      let fields = List.fold_left obj_to_field fields cd.cd_objs in
      List.fold_left params_to_field fields cd.cd_params
    in
    let step =
      let ostep = find_step_method cd in
      let vd_output = var_dec_list param_env ostep.m_outputs in
      let return_ty = ostep.m_outputs |> vd_list_to_type |> (ty param_env) in
      let return_act = Areturn (match vd_output with
                                 | [] -> Evoid
                                 | [vd] -> Eval (Pvar vd.vd_ident)
                                 | vd_l -> Enew (return_ty, List.map (fun vd -> Eval (Pvar vd.vd_ident)) vd_l))
      in
      let body = block param_env ~locals:vd_output ~end_acts:[return_act] ostep.Obc.m_body in
      mk_methode ~args:(var_dec_list param_env ostep.Obc.m_inputs) ~returns:return_ty body "step"
    in
    let reset =
      let oreset = find_reset_method cd in
      let body = block param_env oreset.Obc.m_body in
      mk_methode body "reset"
    in
    let classe = mk_classe ~fields:fields ~constrs:[constructeur] ~methodes:[step;reset] class_name in
    classe::classes
  in
  List.fold_left class_def classes cd_l


let type_dec_list classes td_l =
  let param_env = NamesEnv.empty in
  let _td classes td =
    let classe_name = qualname_to_class_name td.t_name in
    match td.t_desc with
      | Type_abs -> Misc.unsupported "obc2java" 1 (* TODO java *)
      | Type_alias ot -> classes (* TODO java alias ?? *)
      | Type_enum c_l ->
          let mk_constr_enum c = _translate_constructor_name c td.t_name in
          (mk_enum (List.map mk_constr_enum c_l) classe_name) :: classes
      | Type_struct f_l ->
          let mk_field_jfield { Signature.f_name = oname; Signature.f_type = oty } =
            let jty = ty param_env oty in
            let field = Idents.ident_of_name (translate_field_name oname) in (* TODO java pretty ugly *)
            mk_field jty field
          in
          (mk_classe ~fields:(List.map mk_field_jfield f_l) classe_name) :: classes
  in
  List.fold_left _td classes td_l


let const_dec_list cd_l =
  let param_env = NamesEnv.empty in
  let mk_const_field { Obc.c_name = oname ; Obc.c_value = ovalue; Obc.c_type = otype } =
    let name = oname |> translate_const_name |> shortname |> Idents.ident_of_name in (* TODO java pretty ugly*)
    let value = Some (static_exp param_env ovalue) in
    let t = ty param_env otype in
    mk_field ~static:true ~final:true ~value:value t name
  in
  match cd_l with
    | [] -> []
    | _ ->
        let classe_name = "CONSTANTES" |> name_to_classe_name in
        let fields = List.map mk_const_field cd_l in
        [mk_classe ~fields:fields classe_name]


let program p =
  let classes = const_dec_list p.p_consts in
  let classes = type_dec_list classes p.p_types in
  let p = class_def_list classes p.p_defs in
  p



