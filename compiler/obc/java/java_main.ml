open Misc
open Names
open Name_utils
open Modules
open Signature
open Java
open Java_printer

let load_conf () =
  Compiler_options.normalize_register_outputs := true; (* TODO make it work before desactivating *)
  Compiler_options.do_scalarize := true;
  Compiler_options.callgraph_only_on_higherorder := true;
  Compiler_options.functions_are_classes := false;
  ()

(** returns the vd and the pat of a fresh ident from [name] *)
let mk_var ty is_alias name =
  let id = Idents.gen_var "java_main" name in
  mk_var_dec id is_alias ty, Pvar id, Evar id


let program p =
  let p_java = Obc2java.program p in
  let dir = Compiler_utils.build_path "java" in
  Compiler_utils.ensure_dir dir;

  (* Compile and output the nodes *)
  output_program dir p_java;

  (* Create a runnable main simulation *)
  if !Compiler_options.simulation
  then (
    let q_main =
      try !Compiler_options.simulation_node |> qualify_value
      with Not_found ->
        Format.eprintf "Unable to find main node: %s@." !Compiler_options.simulation_node;
        raise Errors.Error
    in
    let sig_main = find_value q_main in
    let ty_main = sig_main.node_outputs |> types_of_arg_list |> prod in
    let ty_main_args = sig_main.node_params |> types_of_param_list in
    let class_name = Obc2java.fresh_classe (!Compiler_options.simulation_node ^ "_sim") in
    Idents.enter_node class_name;
    let field_step_dnb, id_step_dnb =
      let id = Idents.gen_var "java_main" "default_step_nb" in
      mk_field ~static:true ~final:true ~value:(Some (Sint 100)) Tint id, id
    in
    let main_methode =

      (* step is the current iteration step *)
      let vd_step, pat_step, exp_step = mk_var Tint false "step" in

      let vd_args, _, exp_args =
        mk_var (Tarray (Tclass (Names.pervasives_qn "String"), [Sint 0])) false "args" in

      let get_arg i = Earray_elem(exp_args, [Sint i]) in

      let body =
        let out = Eclass(Name_utils.qualname_of_string "java.lang.System.out") in
        let jint = Eclass(Name_utils.qualname_of_string "Integer") in
        let jfloat = Eclass(Name_utils.qualname_of_string "Float") in
        let jbool = Eclass(Name_utils.qualname_of_string "Boolean") in
        let jsys = Eclass(Name_utils.qualname_of_string "java.lang.System") in
        let jminus = pervasives_qn "-" in

        (* num args to give to the main *)
        let rec num_args = List.length ty_main_args in

        (* parse arguments to give to the main *)
        let rec parse_args t_l i = match t_l with
          | [] -> []
          | (Ttype t)::t_l when t = Initial.tint ->
              (Emethod_call(jint, "parseInt", [get_arg i]))
              :: parse_args t_l (i+1)
          | (Ttype t)::t_l when t = Initial.tfloat ->
              (Emethod_call(jfloat, "parseFloat", [get_arg i]))
              :: parse_args t_l (i+1)
          | (Ttype t)::t_l when t = Initial.tint ->
              (Emethod_call(jbool, "parseBool", [get_arg i]))
              :: parse_args t_l (i+1)
          | _ -> Misc.unsupported "java main does not support parsing complexe static args"
        in
        let main_args = parse_args ty_main_args 0 in
        let vd_main, e_main, q_main, ty_main =
       (*   if Modules.is_statefull q_main
          then *)
            let q_main = Obc2java.qualname_to_package_classe q_main in
            let id = Idents.gen_var "java_main" "main" in
            Anewvar(mk_var_dec id false (Tclass q_main), Enew (Tclass q_main, main_args)),
            Emethod_call(Evar id, "step", []),
            q_main,
            ty_main
          (*else
            let q_main = Obc2java.translate_fun_name q_main in
            Aexp Evoid,
            Efun(q_main, main_args),
            q_main,
            ty_main*)
        in
        let acts =
          let parse_max_iteration =
            (* no more arg to give to main, the last one if it exists is the iteration nb *)
            Aifelse(Efun(Names.pervasives_qn ">", [ Efield (exp_args, "length"); Sint num_args ]),
                    (* given max number of iterations *)
                    mk_block [Aassgn(pat_step,
                              Emethod_call(jint, "parseInt", [get_arg num_args]))],
                    (* default max number of iterations *)
                    mk_block [Aassgn(pat_step, Evar id_step_dnb)]);
          in
          let ty_ret = Obc2java.ty NamesEnv.empty ty_main in
          let vd_ret, _, exp_ret = mk_var ty_ret false "ret" in
          let call_main = match ty_ret with
            | Tunit -> Aexp e_main
            | _ -> Anewvar (vd_ret, e_main)
          in
          let print_ret i = match ty_ret with
            | Tunit -> Aexp (Emethod_call(out, "printf", [Sstring "%d => \n"; Evar i]))
            | _ ->
              Aexp (
                Emethod_call(out, "printf",
                             [Sstring "%d => %s\n";
                              Evar i;
                              Emethod_call(java_pervasives, "genToString", [exp_ret])]))
          in
          let main_for_loop i = [call_main; print_ret i] in
          let vd_t1, e_t1 =
            let id = Idents.gen_var "java_main" "t" in
            mk_var_dec id false Tlong, Evar id
          in
          [ Aif(Efun(Names.pervasives_qn "<", [ Efield (exp_args, "length"); Sint num_args ]),
                 mk_block [Aexp (Emethod_call(out, "printf",
                                              [Sstring "error : not enough arguments.\n"]));
                           Areturn Evoid]);
            vd_main;
            parse_max_iteration;
            Anewvar(vd_t1, Emethod_call(jsys, "currentTimeMillis", []));
            Obc2java.fresh_for exp_step main_for_loop;
            Aexp (Emethod_call(out, "printf",
              [ Sstring "time : %d\n";
                Efun(jminus, [Emethod_call(jsys, "currentTimeMillis", []); e_t1])]));
            Aexp(Emethod_call(jsys, "exit", [Sint 0]))
          ]
        in
        mk_block ~locals:[vd_step] acts
      in
      mk_methode ~static:true ~args:[vd_args] ~throws:throws_async body "main"
    in
    let c = mk_classe ~imports:import_async ~fields:[field_step_dnb]
                                            ~methodes:[main_methode] class_name
    in
    output_program dir [c]
  )
