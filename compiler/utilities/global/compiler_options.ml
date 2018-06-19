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

(* Compiler options *)

open Names

(* version of the compiler *)
let version = "1.05.00"
let date = "DATE"

(* standard module *)
let pervasives_module = Pervasives
let standard_lib = "STDLIB"
let standard_lib = try Sys.getenv "HEPTLIB" with Not_found -> standard_lib

(* list of modules initially opened *)
let default_used_modules = ref [pervasives_module]
let set_no_pervasives () = default_used_modules := []

(* load paths *)
let load_path = ref ([standard_lib])


let set_stdlib p =
  load_path := [p]
and add_include d =
  load_path := d :: !load_path;;

(* where is the standard library *)
let locate_stdlib () =
  print_string (try Sys.getenv "HEPTLIB" with Not_found -> standard_lib);
  print_newline ();
  exit 0

let show_version () =
  Format.printf "The Heptagon compiler, version %s (%s)@."
    version date;
  Format.printf
    "This program is free software and comes with ABSOLUTELY NO WARRANTY.@.";
  locate_stdlib ()


(* other options of the compiler *)
let verbose = ref false
let print_types = ref false

let assert_nodes : name list ref = ref []
let add_assert nd = assert_nodes := nd :: !assert_nodes

let simulation = ref false
let simulation_node : name ref = ref ""
let set_simulation_node s =
  simulation := true;
  simulation_node := s

let hepts_simulation = ref false

let create_object_file = ref false

let boolean = ref false

let nosink = ref false

(* Target languages list for code generation *)
let target_languages : string list ref = ref []

let add_target_language s =
  if s = "z3z" then boolean := true; (* TODO use load_conf instead *)
  target_languages := s :: !target_languages

(* Optional path for generated files (C or Java) *)
let target_path : string option ref = ref None

let set_target_path path =
  target_path := Some path

let full_type_info = ref false

let stateful_info = ref false

let full_name = ref false

let nbvars = ref false

let causality = ref true
let init = ref true

let inline : qualname list ref = ref []
let add_inlined_node s = inline := s :: !inline

let flatten = ref false

let deadcode = ref false

let tomato = ref false

let tomato_nodes : qualname list ref = ref []

let add_tomato_node s = tomato_nodes := s :: !tomato_nodes

let tomato_check : qualname list ref = ref []

let add_tomato_check s = tomato_check := s :: !tomato_check

let do_iterator_fusion = ref false

let do_scalarize = ref false
let do_simplify = ref true

let do_mem_alloc = ref false
let do_linear_typing = ref false

let do_mem_alloc_and_typing () =
  do_mem_alloc := true;
  do_linear_typing := true

let use_old_scheduler = ref false
let use_simple_scheduler = ref false

let strict_ssa = ref false
(* if this option is on, generate code that first copies the whole
   array and then modifies one element.  Otherwise, generate two loops
   so that each element in the array is only assigned once. *)
let memcpy_array_and_struct = ref true

let set_strict_ssa () =
  strict_ssa := true;
  memcpy_array_and_struct := false

let unroll_loops = ref false

let optim = ref false
let do_optim () =
  (*  do_iterator_fusion := true; *)(*TODO reset when itfusion is fixed *)
  do_mem_alloc_and_typing ();
  tomato := true;
  deadcode := true

let warn_untranslatable = ref true                             (* z3z | ctrln *)
let abstract_infinite = ref false                                    (* ctrln *)
let warn_abstractions = ref true                                     (* ctrln *)

let check_options () =
  let err m = raise (Arg.Bad m) in
  if !strict_ssa
  then (
    if !do_mem_alloc then err "Unable to activate memory allocation with strict SSA activated.";
    if !do_linear_typing then err "Unable to activate linear typing with strict SSA activated."
  )

let interf_all = ref false

let time_passes = ref false

let doc_verbose = "\t\t\tSet verbose mode"
and doc_version = "\t\tThe version of the compiler"
and doc_print_types = "\t\t\tPrint types"
and doc_include = "<dir>\t\tAdd <dir> to the list of include directories"
and doc_stdlib = "<dir>\t\tDirectory for the standard library"
and doc_object_file = "\t\t\tOnly generate a .epo object file"
and doc_sim = "<node>\t\tCreate simulation for node <node>"
and doc_hepts = "\t\tSimulation for hepts (graphical simulator)"
and doc_locate_stdlib = "\t\tLocate standard libray"
and doc_no_pervasives = "\tDo not load the pervasives module"
and doc_flatten = "\t\tInline everything."
and doc_target =
  "<lang>\tGenerate code in language <lang>\n\t\t\t(with <lang>=c,"
  ^ " java, z3z or ctrln)"
and doc_full_type_info = "\t\t\tPrint full type information"
and doc_stateful_info = "\t\tPrint stateful information"
and doc_full_name = "\t\tPrint full variable name information"
and doc_nbvars = "\t\tPrint information about number of variables"
and doc_target_path =
  "<path>\tGenerated files will be placed in <path>\n\t\t\t(the directory is"
  ^ " cleaned)"
and doc_boolean = "\t\tTranslate enumerated values towards boolean vectors"
and doc_nosink = "\t\tSuppress the sink state in sigali equations"
and doc_deadcode = "\t\tDeadcode removal"
and doc_nocaus = "\t\tDisable causality analysis"
and doc_noinit = "\t\tDisable initialization analysis"
and doc_assert = "<node>\tInsert run-time assertions for boolean node <node>"
and doc_inline = "<node>\tInline node <node>"
and doc_itfusion = "\t\tEnable iterator fusion."
and doc_tomato = "\t\tEnable automata minimization."
and doc_strict_ssa = "\t\tEnsure that the generated code is SSA, even for array elements."
and doc_memalloc = "\t\tEnable memory allocation and linear annotations"
and doc_memalloc_only = "\tEnable memory allocation"
and doc_linear_only = "\t\tEnable linear annotations"
and doc_interf_scheduler = "\tUse the old scheduler"
and doc_simple_scheduler = "\tUse a very simple, time-efficient scheduler"
and doc_optim = "\t\t\tOptimize with deadcode, tomato, itfusion and memalloc"
and doc_interf_all = "\t\tPerform memory allocation on all types"
and doc_unroll = "\t\tUnroll all loops"
and doc_time_passes = "\t\tTime compilation passes"
and doc_abstract_infinite = "\tAbstract infinite state (implied for z3z target)"
and doc_no_warn_untranslat = "\tSuppress warnings about untranslatable constructs"
and doc_no_warn_abstractions = "\tSuppress abstraction warnings"
