
open Java
open Java_printer


let program p =
  let p_java = Obc2java.program p in
  let dir = Compiler_utils.build_path "java" in
  Compiler_utils.ensure_dir dir;
  output_program dir p_java