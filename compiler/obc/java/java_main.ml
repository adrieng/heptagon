open Misc
open Names
open Signature
open Java
open Java_printer

(** returns the vd and the pat of a fresh ident from [name] *)
let mk_var ty name =
  let id = Idents.gen_var "java_main" name in
  mk_var_dec id ty, Pvar id

let program p =
  (*Scalarize*)
  let p = Compiler_utils.pass "Scalarize" true Scalarize.program p Obc_compiler.pp in
  let p_java = Obc2java.program p in
  let dir = Compiler_utils.build_path "java" in
  Compiler_utils.ensure_dir dir;

  (* Compile and output the nodes *)
  output_program dir p_java;

  (* Create a runnable main simulation *)
  if !Compiler_options.simulation
  then (
    let class_name = Obc2java.fresh_classe (!Compiler_options.simulation_node ^ "_sim") in
    Idents.enter_node class_name;
    let field_step_dnb, id_step_dnb =
      let id = Idents.gen_var "java_main" "default_step_nb" in
      mk_field ~static:true ~final:true ~value:(Some (Sint 30000)) Tint id, id
    in
    let main_methode =
      let vd_step, pat_step = mk_var Tint "step" in
      let vd_args, pat_args =
        mk_var (Tarray (Tclass (Names.pervasives_qn "String"), (Sint 0))) "args" in
      let body =
        let vd_main, e_main, q_main, ty_main =
          let q_main = !Compiler_options.simulation_node |> Modules.qualify_value in (*qual*)
          let ty_main =
            (Modules.find_value q_main).node_outputs |> types_of_arg_list |> Types.prod in
          let q_main = Obc2java.qualname_to_package_classe q_main in (*java qual*)
          let id = Idents.gen_var "java_main" "main" in
          mk_var_dec id (Tclass q_main), Eval (Pvar id), q_main, ty_main
        in
        let acts =
          let integer = Eval(Pclass(Names.pervasives_qn "Integer")) in
          let args1 = Eval(Parray_elem(pat_args, Sint 1)) in
          let out = Eval(Pclass(Names.qualname_of_string "java.lang.System.out")) in
          let jarrays = Eval(Pclass(Names.qualname_of_string "java.util.Arrays")) in
          let jint = Eval(Pclass(Names.qualname_of_string "Integer")) in
          let jfloat = Eval(Pclass(Names.qualname_of_string "Float")) in
          let jbool = Eval(Pclass(Names.qualname_of_string "Boolean")) in
          let ret = Emethod_call(e_main, "step", []) in
          let print_ret = match ty_main with
            | Types.Tarray (Types.Tarray _, _) -> Emethod_call(jarrays, "deepToString", [ret])
            | Types.Tarray _ -> Emethod_call(jarrays, "toString", [ret])
            | t when t = Initial.tint -> Emethod_call(jint, "toString", [ret])
            | t when t = Initial.tfloat -> Emethod_call(jfloat, "toString", [ret])
            | t when t = Initial.tbool -> Emethod_call(jbool, "toString", [ret])
            | _ -> Emethod_call(ret, "toString", [])
          in
          [ Anewvar(vd_main, Enew (Tclass q_main, []));
            Aifelse( Efun(Names.pervasives_qn ">", [Eval (Pfield (pat_args, "length")); Sint 1])
                   , mk_block [Aassgn(pat_step, Emethod_call(integer, "parseInt", [args1]))]
                   , mk_block [Aassgn(pat_step, Eval (Pvar id_step_dnb))]);
            Obc2java.fresh_for (Eval pat_step)
              (fun i ->
                [Aexp (Emethod_call(out, "printf",
                                    [Sstring "%d => %s\\n"; Eval (Pvar i); print_ret]))]
              )
          ]
        in
        mk_block ~locals:[vd_step] acts
      in
      mk_methode ~static:true ~args:[vd_args] body "main"
    in
    let c = mk_classe ~fields:[field_step_dnb] ~methodes:[main_methode] class_name in
    output_program dir [c]
  )
