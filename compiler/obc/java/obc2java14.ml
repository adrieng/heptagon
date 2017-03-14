(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)

(** An Obc.program is a Java.package,
       Obc.type_dec, Obc.class_def are Java.classs
       Obc.const_dec is defined in the special class CONSTANTES
       Obc.Lvar are Pvar
       Obc.Lmem are this.Pvar (Pfield)
       Obc.Oobj and Oarray are simply Pvar and Parray_elem
       Obc.Types_alias are dereferenced since no simple type alias is possible in Java *)

(** Requires scalarized Obc :
  [p = e] when [e] is an array is understand as a copy of the reference, not a copy of the array.*)

open Format
open Names
open Modules
open Signature
open Obc
open Obc_utils
open Java

let this_field_ident id = Efield (Ethis, Idents.name id)

(** Additional classes created during the translation *)
let add_classe, get_classes =
  let extra_classes = ref [] in
   (fun c -> extra_classes := c :: !extra_classes)
  ,(fun () -> !extra_classes)

(** fresh Afor from 0 to [size]
    with [body] a function from [var_ident] (the iterator) to [act] list *)
let fresh_for size body =
  let i = Idents.gen_var "obc2java" "i" in
  let id = Java.mk_var_dec i false Tint in
  Java.Afor (id, Sint 0, size, Java.mk_block (body i))

(** fresh nested Afor from 0 to [size]
    with [body] a function from [var_ident] list (the iterator list) to [act] list :
    s_l = [10; 20]
    then
    for i in 20
      for j in 10
        body [i][j]
    *)
let fresh_nfor s_l body =
  let rec aux s_l i_l = match s_l with
    | [s] ->
        let i = Idents.gen_var "obc2java" "i" in
        let id = (Java.mk_var_dec i false Tint) in
        Java.Afor (id, Sint 0, s, Java.mk_block (body (List.rev (i::i_l))))
    | s::s_l ->
        let i = Idents.gen_var "obc2java" "i" in
        let id = Java.mk_var_dec i false Tint in
        Java.Afor (id, Sint 0, s, Java.mk_block ([aux s_l (i::i_l)]))
    | [] -> Misc.internal_error "Fresh nfor called with empty size list"
  in
  aux s_l []

 (* current module is not translated to keep track,
    there is no issue since printed without the qualifier *)
let translate_modul m = m (*match m with
  | Pervasives
  | LocalModule -> m
  | _ when m = g_env.current_mod -> m
  | Module n ->  Module n
  | QualModule { qual = q; name = n} ->
      QualModule { qual = translate_modul q; name = String.lowercase n }
*)

(** a [Module.const] becomes a [module.CONSTANTES.CONST] *)
let translate_const_name { qual = m; name = n } =
  { qual = QualModule { qual = translate_modul m; name = "CONSTANTES"};
    name = String.uppercase_ascii n }

(** a [Module.fun] becomes a [module.FUNS.fun] *)
let translate_fun_name { qual = m; name = n } =
  { qual = QualModule { qual = translate_modul m; name = "FUNS"}; name = n }

(** a [Module.name] becomes a [module.Name]
    used for type_names, class_names, fun_names *)
let qualname_to_class_name q =
  { qual = translate_modul q.qual; name = String.capitalize_ascii q.name }

(** a [Module.name] becomes a [module.Name] even on current_mod *)
let qualname_to_package_classe q =
  { qual = translate_modul q.qual; name = String.capitalize_ascii q.name }

(** Create a fresh class qual from a name *)
let fresh_classe n = Modules.fresh_value "obc2java" n |> qualname_to_package_classe

(** a [Module.Constr] of an [Module.enum] type
    becomes a [module.Enum.CONSTR] of the [module.Enum] class *)
let translate_constructor_name_2 q q_ty =
  let classe = qualname_to_class_name q_ty in
  { qual = QualModule classe; name = String.uppercase_ascii q.name }

let translate_constructor_name q =
  match Modules.unalias_type (Types.Tid (Modules.find_constrs q)) with
    | Types.Tid q_ty when q_ty = Initial.pbool -> q |> shortname |> local_qn
    | Types.Tid q_ty -> translate_constructor_name_2 q q_ty
    | _ -> assert false

let translate_field_name f = f |> Names.shortname |> String.lowercase_ascii

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
  | Types.Sstring s -> Sstring s
  | Types.Sconstructor c -> let c = translate_constructor_name c in Sconstructor c
  | Types.Sfield _ -> eprintf "ojSfield @."; assert false;
  | Types.Stuple se_l ->  tuple param_env se_l
  | Types.Sarray_power (see,pow_list) ->
      let pow_list = List.rev pow_list in
      let rec make_array tyl pow_list = match tyl, pow_list with
        | Tarray(t, _), pow::pow_list ->
            let pow = (try Static.int_of_static_exp Names.QualEnv.empty pow
                       with  Errors.Error ->
                                   eprintf "%aStatic power of array should have integer power. \
                                           Please use callgraph or non-static exp in %a.@."
                              Location.print_location se.Types.se_loc
                              Global_printer.print_static_exp se;
                              raise Errors.Error)
            in
            Enew_array (tyl, Misc.repeat_list (make_array t pow_list) pow)
        | _ -> static_exp param_env see
      in
      make_array (ty param_env se.Types.se_ty) pow_list
        (*let t = match x.pat_ty with
          | Tarray (t,_) -> t
          | _ -> Misc.internal_error "mls2obc select slice type" 5
        in
      let eval_int pow = (try Static.int_of_static_exp Names.QualEnv.empty pow
                          with  Errors.Error ->
                                       eprintf "%aStatic power of array should have integer power. \
                                               Please use callgraph or non-static exp in %a.@."
                                Location.print_location se.Types.se_loc
                                Global_printer.print_static_exp se;
                                raise Errors.Error)
      in
      let rec make_matrix acc = match pow_list with
        | [] -> acc
        | pow :: pow_list ->
              let pow = eval_int pow in
              make_matrix (Misc.repeat_list acc pow) pow_list
      in
      let se_l = match pow_list with
        | [] -> Misc.internal_error "Empty power list" 0
        | pow :: pow_list -> make_matrix (Misc.repeat_list (static_exp param_env see)) pow_list
      in
      Enew_array (ty param_env se.Types.se_ty, se_l)*)
  | Types.Sarray se_l ->
      Enew_array (ty param_env se.Types.se_ty, List.map (static_exp param_env) se_l)
  | Types.Srecord f_e_l ->
      let ty_name =
        match se.Types.se_ty with
        | Types.Tid ty_name -> qualname_to_package_classe ty_name
        | _ -> Misc.internal_error "Obc2java14"
      in
      let f_e_l =
        List.sort
          (fun (f1,_) (f2,_) -> compare f1.name f2.name)
          f_e_l in
      let e_l = List.map (fun (_f,e) -> e) f_e_l in
      Enew (Tclass ty_name, List.map (static_exp param_env) e_l)
  | Types.Sop (f, se_l) -> Efun (f, List.map (static_exp param_env) se_l)

and boxed_ty param_env t = match Modules.unalias_type t with
  | Types.Tprod [] -> Tunit
  | Types.Tprod ty_l -> tuple_ty param_env ty_l
  | Types.Tid t when t = Initial.pbool -> Tclass (Names.local_qn "Boolean")
  | Types.Tid t when t = Initial.pint -> Tclass (Names.local_qn "Integer")
  | Types.Tid t when t = Initial.pfloat -> Tclass (Names.local_qn "Float")
  | Types.Tid t ->
      begin try
        let ty = find_type t in
        begin match ty with
        | Tenum _ -> Tint
        | _ -> Tclass (qualname_to_class_name t)
        end
      with Not_found -> Tclass (qualname_to_class_name t)
      end
  | Types.Tarray _ ->
    let rec gather_array t = match t with
      | Types.Tarray (t,size) ->
          let t, s_l = gather_array t in
          t, (static_exp param_env size)::s_l
      | _ -> ty param_env t, []
    in
    let t, s_l = gather_array t in
    Tarray (t, s_l)
  | Types.Tinvalid -> Misc.internal_error "obc2java invalid type"

and tuple_ty _param_env ty_l =
  let ln = ty_l |> List.length |> Pervasives.string_of_int in
  Tclass (java_pervasive_class ("Tuple"^ln))

and ty param_env t =
  let t = Modules.unalias_type t in
  match t with
  | Types.Tprod [] -> Tunit
  | Types.Tprod ty_l -> tuple_ty param_env ty_l
  | Types.Tid t when t = Initial.pbool -> Tbool
  | Types.Tid t when t = Initial.pint -> Tint
  | Types.Tid t when t = Initial.pfloat -> Tfloat
  | Types.Tid t ->
      begin try
        let ty = find_type t in
        begin match ty with
        | Tenum _ -> Tint
        | _ -> Tclass (qualname_to_class_name t)
        end
      with Not_found -> Tclass (qualname_to_class_name t)
      end
  | Types.Tarray _ ->
      let rec gather_array t = match t with
        | Types.Tarray (t,size) ->
            let tin, s_l = gather_array t in
            tin, (static_exp param_env size)::s_l
        | _ -> ty param_env t, []
      in
      let tin, s_l = gather_array t in
      Tarray (tin, s_l)
  | Types.Tinvalid -> Misc.internal_error "obc2java invalid type"

and var_dec param_env vd = { vd_type = ty param_env vd.v_type;
                             vd_alias = vd.v_alias;
                             vd_ident = vd.v_ident }

and var_dec_list param_env vd_l = List.map (var_dec param_env) vd_l

and exp param_env e = match e.e_desc with
  | Obc.Eextvalue p -> ext_value param_env p
  | Obc.Eop (op,e_l) -> Efun (op, exp_list param_env e_l)
  | Obc.Estruct (ty_name,f_e_l) ->
      let ty_name = qualname_to_package_classe ty_name in
      let f_e_l =
        List.sort
          (fun (f1,_) (f2,_) -> compare f1.name f2.name)
          f_e_l in
      let e_l = List.map (fun (_f,e) -> e) f_e_l in
      Enew (Tclass ty_name, exp_list param_env e_l)
  | Obc.Earray e_l -> Enew_array (ty param_env e.e_ty, exp_list param_env e_l)

and exp_list param_env e_l = List.map (exp param_env) e_l

and tuple param_env se_l =
  let t = tuple_ty param_env (List.map (fun e -> Modules.unalias_type e.Types.se_ty) se_l) in
  Enew (t, List.map (static_exp param_env) se_l)


and pattern param_env p = match p.pat_desc with
  | Obc.Lvar v -> Pvar v
  | Obc.Lmem v -> Pthis v
  | Obc.Lfield (p,f) -> Pfield (pattern param_env p, translate_field_name f)
  | Obc.Larray _ ->
      let p, idx_l =
        let rec gather_idx acc p = match p.pat_desc with
          | Obc.Larray (p,e) -> gather_idx ((exp param_env e)::acc) p
          | _ -> pattern param_env p, acc
        in
        let p, idx_l = gather_idx [] p in
        p, idx_l
      in
      Parray_elem (p, idx_l)

and pattern_to_exp param_env p = match p.pat_desc with
  | Obc.Lvar v -> Evar v
  | Obc.Lmem v -> this_field_ident v
  | Obc.Lfield (p,f) ->
    Efield (pattern_to_exp param_env p, translate_field_name f)
  | Obc.Larray _ ->
      let p, idx_l =
        let rec gather_idx acc p = match p.pat_desc with
          | Obc.Larray (p,e) -> gather_idx ((exp param_env e)::acc) p
          | _ -> pattern_to_exp param_env p, acc
        in
        let p, idx_l = gather_idx [] p in
        p, idx_l
      in
      Earray_elem (p, idx_l)

and ext_value param_env w = match w.w_desc with
  | Obc.Wvar v -> Evar v
  | Obc.Wconst c -> static_exp param_env c
  | Obc.Wmem v -> this_field_ident v
  | Obc.Wfield (p,f) -> Efield (ext_value param_env p, translate_field_name f)
  | Obc.Warray (p,e) -> Earray_elem (ext_value param_env p, [exp param_env e])


let obj_ref param_env o = match o with
  | Oobj id -> Evar id
  | Oarray (id, p_l) ->
      (* the generated list is in java order *)
      let idx_l = List.map (fun p -> pattern_to_exp param_env p) p_l in
      Earray_elem (Evar id, idx_l)

let jop_of_op param_env op_name e_l =
  match op_name with
  | { qual = Module "Iostream"; name = "printf" } ->
      Emethod_call (Eclass(Names.qualname_of_string "java.lang.System.out"),
                    "print",
                    (exp_list param_env e_l))
  | _ ->
      Efun (op_name, exp_list param_env e_l)


let rec act_list param_env act_l acts =
  let _act act acts = match act with
    | Obc.Aassgn (p,e) -> (Java.Aassgn (pattern param_env p, exp param_env e))::acts
    | Obc.Aop (op,e_l) -> Aexp (jop_of_op param_env op e_l) :: acts
    | Obc.Acall (p_l, obj, Mstep, e_l) ->
        let o_ref = obj_ref param_env obj in
        let ecall = Emethod_call (o_ref, "step", exp_list param_env e_l) in
        let assgn = Aexp ecall in
        let copy_return_to_var i p =
          let p = pattern param_env p in
          Java.Aassgn (p, Emethod_call (o_ref, "getOutput" ^ (string_of_int i), []))
        in
        let copies = Misc.mapi copy_return_to_var p_l in
        assgn::(copies@acts)
    | Obc.Acall (_, obj, Mreset, _) ->
        let acall = Emethod_call (obj_ref param_env obj, "reset", []) in
        Aexp acall::acts
    | Obc.Acase (e, c_b_l) when e.e_ty = Types.Tid Initial.pbool ->
        (match c_b_l with
          | [] -> acts
          | [(c,b)] when c = Initial.ptrue ->
              (Aif (exp param_env e, block param_env b)):: acts
          | [(c,b)] when c = Initial.pfalse ->
              (Aifelse (exp param_env e, {Java.b_locals = [];
                                          Java.b_body = []}, block param_env b)) :: acts
          | _ ->
              let _, _then = List.find (fun (c,_) -> c = Initial.ptrue) c_b_l in
              let _, _else = List.find (fun (c,_) -> c = Initial.pfalse) c_b_l in
              (Aifelse (exp param_env e, block param_env _then, block param_env _else)) :: acts)
    | Obc.Acase (e, c_b_l) ->
        let _c_b (c,b) =
          let type_name =
            match e.e_ty with
              Types.Tid n -> qualname_to_package_classe n
            | _ -> failwith("act_list: translating case") in
          let c = translate_constructor_name_2 c type_name in
          Sexp(Sconstructor c),
          block param_env b in
        let acase = Aswitch (exp param_env e, List.map _c_b c_b_l) in
        acase::acts
    | Obc.Afor (v, se, se', b) ->
        let afor = Java.Afor (var_dec param_env v,
                        exp param_env se, exp param_env se', block param_env b) in
        afor::acts
    | Obc.Ablock b ->
        let ablock = Java.Ablock (block param_env b) in
        ablock::acts
  in
  List.fold_right _act act_l acts

and block param_env ?(locals=[]) ?(end_acts=[]) ob =
  let blocals = var_dec_list param_env ob.Obc.b_locals in
  let locals = locals @ blocals in
  let acts = act_list param_env ob.Obc.b_body end_acts in
  { Java.b_locals = locals; Java.b_body = acts }





(** Create the [param_env] and translate [Signature.param]s to [var_dec]s
   @return [vds, param_env] *)
let sig_params_to_vds p_l =
  let param_to_arg param_env p =
    let p_ident = Idents.gen_var "obc2java" (String.uppercase_ascii p.Signature.p_name) in
    let p_vd = Java.mk_var_dec p_ident false (ty param_env p.Signature.p_type) in
    let param_env = NamesEnv.add p.Signature.p_name p_ident param_env in
    p_vd, param_env
  in Misc.mapfold param_to_arg NamesEnv.empty p_l

(** Translate [Signature.arg]s to [var_dec]s *)
let sig_args_to_vds param_env a_l =
  let arg_to_vd { a_name = n; a_type = t } =
    let n = match n with None -> "v" | Some s -> s in
    let id = Idents.gen_var "obc2java" n in
    Java.mk_var_dec id false (ty param_env t)
  in List.map arg_to_vd a_l

(** [copy_to_this vd_l] creates [this.x = x] for all [x] in [vd_l] *)
let copy_to_this vd_l =
  let _vd vd = Java.Aassgn (Pthis vd.vd_ident, Evar vd.vd_ident) in
  List.map _vd vd_l


let class_def_list classes cd_l =
  let class_def classes cd =
    Idents.enter_node cd.cd_name;
    let class_name = qualname_to_package_classe cd.cd_name in
    (* [param_env] is an env mapping local param name to ident *)
    (* [params] : fields to stock the static parameters, arguments of the constructors *)
    let fields_params, vds_params, _exps_params, param_env =
      let v, env = sig_params_to_vds cd.cd_params in
      let f = vds_to_fields ~protection:Pprotected v in
      let e = vds_to_exps v in
      f, v, e, env
    in
    (* [reset] is the reset method of the class,
       [reset_mems] is the block to reset the members of the class
         without call to the reset method of inner instances,
         it retains [this.x = 0] but not [this.I.reset()] *)
    let reset, reset_mems =
      try (* When there exist a reset method *)
        let oreset = find_reset_method cd in
        let body = block param_env oreset.Obc.m_body in
        let reset_mems = block param_env (remove_resets oreset.Obc.m_body) in
        mk_methode body "reset", reset_mems
      with Not_found -> (* stub reset method *)
        mk_methode (Java.mk_block []) "reset", Java.mk_block []
    in
     (* [obj_env] gives the type of an [obj_ident],
        needed in async because we change the classe for async obj *)
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
                (Java.Aassgn (Pthis od.o_ident, Enew (t, params)))::acts
            | Some size_l ->
                let size_l = List.rev (List.map (static_exp param_env) size_l) in
                let t = Idents.Env.find od.o_ident obj_env in
                let assgn_elem i_l =
                  [ Java.Aassgn (Parray_elem (Pthis od.o_ident, List.map mk_var i_l),
                                 Enew (t, params)) ]
                in
                (Java.Aassgn (Pthis od.o_ident, Enew_array (Tarray (t,size_l), [])))
                 :: (fresh_nfor size_l assgn_elem)
                 :: acts
        in
        (* function to allocate the arrays *)
        let allocate acts vd = match Modules.unalias_type vd.v_type with
          | Types.Tarray _ ->
              let t = ty param_env vd.v_type in
              ( Java.Aassgn (Pthis vd.v_ident, Enew_array (t,[])) ):: acts
          | _ -> acts
        in
        (* init actions [acts] in reverse order : *)
        (* init member variables *)
        let acts = [Java.Ablock reset_mems] in
        (* allocate member arrays *)
        let acts = List.fold_left allocate acts cd.cd_mems in
        (* init member objects *)
        let acts = List.fold_left obj_init_act acts cd.cd_objs in
        (* init static params *)
        let acts = (copy_to_this vds_params)@acts in
        { Java.b_locals = []; Java.b_body = acts }
      in mk_methode ~args:vds_params body (shortname class_name), obj_env
    in
    let fields =
      let mem_to_field fields vd =
        (Java.mk_field ~protection:Pprotected (ty param_env vd.v_type) vd.v_ident) :: fields
      in
      let obj_to_field fields od =
        let jty = match od.o_size with
          | None -> Idents.Env.find od.o_ident obj_env
          | Some size_l -> Tarray (Idents.Env.find od.o_ident obj_env,
                                   List.map (static_exp param_env) size_l)
        in
        (Java.mk_field ~protection:Pprotected jty od.o_ident) :: fields
      in
      let fields = fields_params in
      let fields = List.fold_left mem_to_field fields cd.cd_mems in
      List.fold_left obj_to_field fields cd.cd_objs
    in
    let ostep = find_step_method cd in
    let vd_output = var_dec_list param_env ostep.m_outputs in
    let output_fields =
      List.map (fun vd -> Java.mk_field vd.vd_type vd.vd_ident) vd_output in
    let fields = fields @ output_fields in
    let build_output_methods i f =
      mk_methode ~returns:f.Java.f_type
        (Java.mk_block [Areturn (Evar f.f_ident)])
        ("getOutput" ^ (string_of_int i))
    in
    let output_methods = Misc.mapi build_output_methods output_fields in
    let step =
      let body = block param_env ostep.Obc.m_body in
      mk_methode ~args:(var_dec_list param_env ostep.Obc.m_inputs) ~returns:Tunit body "step"
    in
    let classe = mk_classe ~fields:fields
                           ~constrs:[constructeur]
                           ~methodes:([step;reset]@output_methods)
                           class_name in
    classe::classes
  in
  List.fold_left class_def classes cd_l


let type_dec_list classes td_l =
  let param_env = NamesEnv.empty in
  let _td classes td =
    let classe_name = qualname_to_package_classe td.t_name in
    Idents.enter_node classe_name;
    match td.t_desc with
      | Type_abs -> Misc.unsupported "obc2java, abstract type."
      | Type_alias t -> (*verify that it is possible to unalias and skip it*)
          let _ = Modules.unalias_type t in
          classes
      | Type_enum c_l ->
          let mk_constr_field (acc_fields,i) c =
            let init_value = Sint i in
            let c = translate_constructor_name_2 c classe_name in
            let field =
              Java.mk_field ~static:true ~final:true ~value:(Some init_value)
                Tint (Idents.ident_of_name c.name) in
            (field::acc_fields),(i+1) in
          let fields,_ = List.fold_left mk_constr_field ([],1) c_l in
          (mk_classe ~fields:(List.rev fields) classe_name) :: classes
      | Type_struct f_l ->
          let mk_field_jfield { Signature.f_name = oname; Signature.f_type = oty } =
            let jty = ty param_env oty in
            let field = Idents.ident_of_name (translate_field_name oname) in
            (* [translate_field_name] will give the right result anywhere it is used,
            since the [ident_of_name] will keep it as it is unique in the class,
            see [Idents.enter_node classe_name] *)
            Java.mk_field jty field
          in
          let f_l =
            List.sort
              (fun f1 f2 ->
                 compare (f1.Signature.f_name.name) (f2.Signature.f_name.name))
              f_l in
          let fields = List.map mk_field_jfield f_l in
          let cons_params = List.map
            (fun f -> Java.mk_var_dec f.f_ident false f.Java.f_type) fields in
          let cons_body =
            List.map
              (fun f -> Java.Aassgn ((Pthis f.f_ident),(Evar f.f_ident)))
              fields in
          let cons =
            mk_methode
              ~args:cons_params
              (Java.mk_block cons_body)
              classe_name.name in
          (mk_classe ~fields:fields ~constrs:[cons] classe_name) :: classes
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
        (* name should always keep the shortname unchanged
            since we enter a special node free of existing variables *)
        (* thus [translate_const_name] will gives the right result anywhere it is used. *)
        let value = Some (static_exp param_env ovalue) in
        let t = ty param_env otype in
        Java.mk_field ~static: true ~final: true ~value: value t name
      in
      let fields = List.map mk_const_field cd_l in
      [mk_classe ~fields: fields classe_name]



let program p =
  let rec program_descs pds (ns,cs,ts) = match pds with
    | [] -> ns,cs,ts
    | Obc.Pclass n :: pds -> program_descs pds (n::ns,cs,ts)
    | Obc.Pconst c :: pds -> program_descs pds (ns,c::cs,ts)
    | Obc.Ptype t :: pds -> program_descs pds (ns,cs,t::ts)
  in
  let ns,cs,ts = program_descs p.p_desc ([],[],[]) in
  let classes = const_dec_list cs in
  let classes = type_dec_list classes ts in
  let p = class_def_list classes ns in
  get_classes()@p
