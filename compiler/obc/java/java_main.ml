
open Java
open Java_printer
open Obc2java
open Compiler_utils


let program p =
  let filename = filename_of_name p.Obc.p_modname in
  let dirname = build_path (filename ^ "_java") in
  let dir = clean_dir dirname in
  let p_java = Obc2java.program p in
  output_program dir p_java