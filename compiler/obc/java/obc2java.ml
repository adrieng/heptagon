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

(** Requires scalar Obc : [p = e] when [e] is an array is understand as a copy of the reference,
  not a copy of the array. *)

open Format
open Misc
open Names
open Modules
open Signature
open Obc
open Obc_utils
open Java


(** Additional classes created during the translation *)
let add_classe, get_classes =
  let extra_classes = ref [] in
   (fun c -> extra_classes := c :: !extra_classes)
  ,(fun () -> !extra_classes)

(** fresh Afor from 0 to [size] with [body] a function from [var_ident] (the iterator) to [act] list *)
let fresh_for size body =
  let i = Idents.gen_var "obc2java" "i" in
  let id = mk_var_dec i Tint in
  Afor (id, Sint 0, size, mk_block (body i))

 (* current module is not translated to keep track, there is no issue since printed without the qualifier *)
let rec translate_modul m = match m with
  | Pervasives
  | LocalModule -> m
  | _ when m = g_env.current_mod -> m
  | Module n ->  Module (String.lowercase n)
  | QualModule { qual = q; name = n} -> QualModule { qual = translate_modul q; name = String.lowercase n }

(** a [Module.const] becomes a [module.CONSTANTES.CONST] *)
let translate_const_name { qual = m; name = n } =
  { qual = QualModule { qual = translate_modul m; name = "CONSTANTES"}; name = String.uppercase n }

(** a [Module.fun] becomes a [module.FUNS.fun] *)
let translate_fun_name { qual = m; name = n } =
  { qual = QualModule { qual = translate_modul m; name = "FUNS"}; name = n }

(** a [Module.name] becomes a [module.Name]
    used for type_names, class_names, fun_names *)
let qualname_to_class_name q =
  { qual = translate_modul q.qual; name = String.capitalize q.name }

(** a [Module.name] becomes a [module.Name] even on current_mod *)
let qualname_to_package_classe q =
  { qual = translate_modul q.qual; name = String.capitalize q.name }

(** Create a fresh class qual from a name *)
let fresh_classe n = Modules.fresh_value "obc2java" n |> qualname_to_package_classe

(** a [Module.Constr] of an [Module.enum] type becomes a [module.Enum.CONSTR] of the [module.Enum] class *)
let translate_constructor_name_2 q q_ty =
  let classe = qualname_to_class_name q_ty in
  { qual = QualModule classe; name = String.uppercase q.name }

let translate_constructor_name q =
  match Modules.find_constrs q with
    | Types.Tid q_ty when q_ty = Initial.pbool -> q |> shortname |> local_qn
    | Types.Tid q_ty -> translate_constructor_name_2 q q_ty
    | _ -> assert false

let translate_field_name f = f |> Names.shortname |> String.lowercase

(** a [name] becomes a [package.Name] *)
let name_to_classe_name n = n |> Modules.current_qual |> qualname_to_package_classe

(** translate an ostatic_exp into an jexp *)
let rec static_exp param_env se = match se.Types.se_desc with
  | Types.Svar c ->
      (match c.qual with
        | LocalModule ->
            let n = NamesEnv.find (shortname c) param_env in
            Svar (n |> Idents.name |> local_qn)
        | _ -> Svar (translate_const_name c))
  | Types.Sint i -> Sint i
  | Types.Sfloat f -> Sfloat f
  | Types.Sbool b -> Sbool b
  | Types.Sconstructor c -> let c = translate_constructor_name c in Sconstructor c
  | Types.Sfield f -> eprintf "ojSfield @."; assert false;
  | Types.Stuple se_l ->  tuple param_env se_l
  | Types.Sarray_power (see,pow) ->
      let pow = (try Static.int_of_static_exp Names.QualEnv.empty pow
                 with Errors.Error ->
                   eprintf "%aStatic power of array should have integer power. \
                            Please use callgraph or non-static exp in %a.@."
                           Location.print_location se.Types.se_loc
                           Global_printer.print_static_exp se;
                   raise Errors.Error)
      in
      let se_l = Misc.repeat_list (static_exp param_env see) pow in
      Enew_array (ty param_env se.Types.se_ty, se_l)
  | Types.Sarray se_l -> Enew_array (ty param_env se.Types.se_ty, List.map (static_exp param_env) se_l)
  | Types.Srecord _ -> eprintf "ojSrecord@."; assert false; (* TODO java *)
  | Types.Sop (f, se_l) -> Efun (qualname_to_class_name f, List.map (static_exp param_env) se_l)

and boxed_ty param_env t = match t with
  | Types.Tprod ty_l -> tuple_ty param_env ty_l
  | Types.Tid t when t = Initial.pbool -> Tclass (Names.local_qn "Boolean")
  | Types.Tid t when t = Initial.pint -> Tclass (Names.local_qn "Integer")
  | Types.Tid t when t = Initial.pfloat -> Tclass (Names.local_qn "Float")
  | Types.Tid t -> Tclass (qualname_to_class_name t)
  | Types.Tarray (t,size) -> Tarray (boxed_ty param_env t, static_exp param_env size)
  | Types.Tmutable t -> Tref (boxed_ty param_env t)
  | Types.Tunit -> Tunit

and tuple_ty param_env ty_l =
  let ln = ty_l |> List.length |> Pervasives.string_of_int in
  Tclass (java_pervasive_class ("Tuple"^ln))

and ty param_env t :Java.ty = match t with
  | Types.Tprod ty_l -> tuple_ty param_env ty_l
  | Types.Tid t when t = Initial.pbool -> Tbool
  | Types.Tid t when t = Initial.pint -> Tint
  | Types.Tid t when t = Initial.pfloat -> Tfloat
  | Types.Tid t -> Tclass (qualname_to_class_name t)
  | Types.Tarray (t,size) -> Tarray (ty param_env t, static_exp param_env size)
  | Types.Tmutable t -> Tref (ty param_env t)
  | Types.Tunit -> Tunit

and var_dec param_env vd = { vd_type = ty param_env vd.v_type; vd_ident = vd.v_ident }

and var_dec_list param_env vd_l = List.map (var_dec param_env) vd_l

and exp param_env e = match e.e_desc with
  | Obc.Epattern p -> Eval (pattern param_env p)
  | Obc.Econst se -> static_exp param_env se
  | Obc.Eop (op,e_l) -> Efun (op, exp_list param_env e_l)
  | Obc.Estruct _ -> eprintf "ojEstruct@."; assert false (* TODO java *)
  | Obc.Earray e_l -> Enew_array (ty param_env e.e_ty, exp_list param_env e_l)

and exp_list param_env e_l = List.map (exp param_env) e_l

and tuple param_env se_l =
  let t = tuple_ty param_env (List.map (fun e -> e.Types.se_ty) se_l) in
  Enew (t, List.map (static_exp param_env) se_l)


and pattern param_env p = match p.pat_desc with
  | Obc.Lvar v -> Pvar v
  | Obc.Lmem v -> Pthis v
  | Obc.Lfield (p,f) -> Pfield (pattern param_env p, translate_field_name f)
  | Obc.Larray (p,e) -> Parray_elem (pattern param_env p, exp param_env e)

let obj_ref param_env o = match o with
  | Oobj id -> Eval (Pvar id)
  | Oarray (id,p) -> Eval (Parray_elem (Pvar id, Eval (pattern param_env p)))

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
          let t = ty param_env p.pat_ty in
          let cast t e = match t with
            | Tbool -> Ecast(Tbool, Ecast(boxed_ty param_env p.pat_ty, e))
            | Tint -> Ecast(Tint, Ecast(boxed_ty param_env p.pat_ty, e))
            | Tfloat -> Ecast(Tfloat, Ecast(boxed_ty param_env p.pat_ty, e))
            | _ -> Ecast(t, e)
          in
          let p = pattern param_env p in
          Aassgn (p, cast t (Eval (Pfield (Pvar return_id, "c"^(string_of_int i)))))
        in
        let copies = Misc.mapi copy_return_to_var p_l in
        assgn::(copies@acts)
    | Obc.Acall (_, obj, Mreset, _) ->
        let acall = Amethod_call (obj_ref param_env obj, "reset", []) in
        acall::acts
    | Obc.Acase (e, c_b_l) when e.e_ty = Types.Tid Initial.pbool ->
        (match c_b_l with
          | [] -> acts
          | [(c,b)] when c = Initial.ptrue ->
              (Aif (exp param_env e, block param_env b)):: acts
          | [(c,b)] when c = Initial.pfalse ->
              (Aifelse (exp param_env e, {b_locals = []; b_body = []}, block param_env b)) :: acts
          | _ ->
              let _, _then = List.find (fun (c,_) -> c = Initial.ptrue) c_b_l in
              let _, _else = List.find (fun (c,_) -> c = Initial.pfalse) c_b_l in
              (Aifelse (exp param_env e, block param_env _then, block param_env _else)) :: acts)
    | Obc.Acase (e, c_b_l) ->
        let _c_b (c,b) = translate_constructor_name c, block param_env b in
        let acase = Aswitch (exp param_env e, List.map _c_b c_b_l) in
        acase::acts
    | Obc.Afor (v, se, se', b) ->
        let afor = Afor (var_dec param_env v, static_exp param_env se, static_exp param_env se', block param_env b) in
        afor::acts
    | Obc.Ablock b ->
        let ablock = Ablock (block param_env b) in
        ablock::acts
  in
  List.fold_right _act act_l acts

and block param_env ?(locals=[]) ?(end_acts=[]) ob =
  let blocals = var_dec_list param_env ob.Obc.b_locals in
  let locals = locals @ blocals in
  let acts = act_list param_env ob.Obc.b_body end_acts in
  { b_locals = locals; b_body = acts }





(** Create the [param_env] and translate [Signature.param]s to [var_dec]s
   @return [vds, param_env] *)
let sig_params_to_vds p_l =
  let param_to_arg param_env p =
    let p_ident = Idents.gen_var "obc2java" (String.uppercase p.Signature.p_name) in
    let p_vd = { vd_ident = p_ident; vd_type = ty param_env p.Signature.p_type } in
    let param_env = NamesEnv.add p.Signature.p_name p_ident param_env in
    p_vd, param_env
  in Misc.mapfold param_to_arg NamesEnv.empty p_l

(** Translate [Signature.arg]s to [var_dec]s *)
let sig_args_to_vds param_env a_l =
  let arg_to_vd { a_name = n; a_type = t } =
    let n = match n with None -> "v" | Some s -> s in
    let id = Idents.gen_var "obc2java" n in
    mk_var_dec id (ty param_env t)
  in List.map arg_to_vd a_l

(** [copy_to_this vd_l] creates [this.x = x] for all [x] in [vd_l] *)
let copy_to_this vd_l =
  let _vd vd = Aassgn (Pthis vd.vd_ident, Eval (Pvar vd.vd_ident)) in
  List.map _vd vd_l


let class_def_list classes cd_l =
  let class_def classes cd =
    Idents.enter_node cd.cd_name;
    let class_name = qualname_to_package_classe cd.cd_name in
    (* [param_env] is an env mapping local param name to ident *)
    (* [params] : fields to stock the static parameters, arguments of the constructors *)
    let fields_params, vds_params, exps_params, param_env =
      let v, env = sig_params_to_vds cd.cd_params in
      let f = vds_to_fields ~protection:Pprotected v in
      let e = vds_to_exps v in
      f, v, e, env
    in
    (* [reset] is the reset method of the class,
       [reset_mems] is the block to reset the members of the class
         without call to the reset method of inner instances, it retains [this.x = 0] but not [this.I.reset()] *)
    let reset, reset_mems =
      try (* When there exist a reset method *)
        let oreset = find_reset_method cd in
        let body = block param_env oreset.Obc.m_body in
        let reset_mems = block param_env (remove_resets oreset.Obc.m_body) in
        mk_methode body "reset", reset_mems
      with Not_found -> (* stub reset method *)
        mk_methode (mk_block []) "reset", mk_block []
    in
     (* [obj_env] gives the type of an [obj_ident], needed in async because we change the classe for async obj *)
    let constructeur, obj_env =
      let obj_env = (* Mapping between Obc class and Java class, useful at least with asyncs *)
        let aux obj_env od =
          let t = Tclass (qualname_to_class_name od.o_class)
          in Idents.Env.add od.o_ident t obj_env
        in List.fold_left aux Idents.Env.empty cd.cd_objs
      in
      let body =
        (* Function to initialize the objects *)
        let obj_init_act acts od =
          let params = List.map (static_exp param_env) od.o_params in
          match od.o_size with
            | None ->
                let t = Idents.Env.find od.o_ident obj_env in
                (Aassgn (Pthis od.o_ident, Enew (t, params)))::acts
            | Some size ->
                let size = static_exp param_env size in
                let t = Idents.Env.find od.o_ident obj_env in
                let assgn_elem i = [ Aassgn (Parray_elem (Pthis od.o_ident, mk_var i), Enew (t, params)) ] in
                (Aassgn (Pthis od.o_ident, Enew_array (Tarray (t,size), [])))
                 :: (fresh_for size assgn_elem)
                 :: acts
        in
        (* function to allocate the arrays *)
        let allocate acts vd = match vd.v_type with
          | Types.Tarray (t, size) ->
              let t = ty param_env vd.v_type in
              ( Aassgn (Pthis vd.v_ident, Enew_array (t,[])) ):: acts
          | _ -> acts
        in
        (* init actions [acts] in reverse order : *)
        (* init member variables *)
        let acts = [Ablock reset_mems] in
        (* allocate member arrays *)
        let acts = List.fold_left allocate acts cd.cd_mems in
        (* init member objects *)
        let acts = List.fold_left obj_init_act acts cd.cd_objs in
        (* init static params *)
        let acts = (copy_to_this vds_params)@acts in
        { b_locals = []; b_body = acts }
      in mk_methode ~args:vds_params body (shortname class_name), obj_env
    in
    let fields =
      let mem_to_field fields vd = (mk_field ~protection:Pprotected (ty param_env vd.v_type) vd.v_ident) :: fields in
      let obj_to_field fields od =
        let jty = match od.o_size with
          | None -> Idents.Env.find od.o_ident obj_env
          | Some size -> Tarray (Idents.Env.find od.o_ident obj_env, static_exp param_env size)
        in
        (mk_field ~protection:Pprotected jty od.o_ident) :: fields
      in
      let fields = fields_params in
      let fields = List.fold_left mem_to_field fields cd.cd_mems in
      List.fold_left obj_to_field fields cd.cd_objs
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
    let classe = mk_classe ~fields:fields
                           ~constrs:[constructeur] ~methodes:[step;reset] class_name in
    classe::classes
  in
  List.fold_left class_def classes cd_l


let type_dec_list classes td_l =
  let param_env = NamesEnv.empty in
  let _td classes td =
    let classe_name = qualname_to_package_classe td.t_name in
    Idents.enter_node classe_name;
    match td.t_desc with
      | Type_abs -> Misc.unsupported "obc2java, abstract type." 1
      | Type_alias _ -> Misc.unsupported "obc2java, type alias." 2
      | Type_enum c_l ->
          let mk_constr_enum c = translate_constructor_name_2 c td.t_name in
          (mk_enum (List.map mk_constr_enum c_l) classe_name) :: classes
      | Type_struct f_l ->
          let mk_field_jfield { Signature.f_name = oname; Signature.f_type = oty } =
            let jty = ty param_env oty in
            let field = Idents.ident_of_name (translate_field_name oname) in
            (* [translate_field_name] will give the right result anywhere it is used,
            since the [ident_of_name] will keep it as it is unique in the class, see [Idents.enter_node classe_name] *)
            mk_field jty field
          in
          (mk_classe ~fields:(List.map mk_field_jfield f_l) classe_name) :: classes
  in
  List.fold_left _td classes td_l


let const_dec_list cd_l = match cd_l with
  | [] -> []
  | _ ->
      let classe_name = "CONSTANTES" |> name_to_classe_name in
      Idents.enter_node classe_name;
      let param_env = NamesEnv.empty in
      let mk_const_field { Obc.c_name = oname ; Obc.c_value = ovalue; Obc.c_type = otype } =
        let name = oname |> translate_const_name |> shortname |> Idents.ident_of_name in
        (* name should always keep the shortname unchanged since we enter a special node free of existing variables *)
        (* thus [translate_const_name] will gives the right result anywhere it is used. *)
        let value = Some (static_exp param_env ovalue) in
        let t = ty param_env otype in
        mk_field ~static: true ~final: true ~value: value t name
      in
      let fields = List.map mk_const_field cd_l in
      [mk_classe ~fields: fields classe_name]



let program p =
  let classes = const_dec_list p.p_consts in
  let classes = type_dec_list classes p.p_types in
  let p = class_def_list classes p.p_classes in
  get_classes()@p



