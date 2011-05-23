(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* Compiler options *)

open Names

(* version of the compiler *)
let version = "0.4"
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
  print_newline ()

let show_version () =
  Format.printf "The Heptagon compiler, version %s (%s)@."
    version date;
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

(* Target languages list for code generation *)
let target_languages : string list ref = ref []

let add_target_language s =
  target_languages := s :: !target_languages

(* Optional path for generated files (C or Java) *)
let target_path : string option ref = ref None

let set_target_path path =
  target_path := Some path

let java_queue_size = ref 0

let full_type_info = ref false

let full_name = ref false

let causality = ref true
let init = ref true

let inline : qualname list ref = ref []
let add_inlined_node s = inline := s :: !inline

let flatten = ref false

let tomato = ref false

let tomato_nodes : qualname list ref = ref []

let add_tomato_node s = tomato_nodes := s :: !tomato_nodes

let tomato_check : qualname list ref = ref []

let add_tomato_check s = tomato_check := s :: !tomato_check

let do_iterator_fusion = ref false

let do_scalarize = ref false

let doc_verbose = "\t\t\tSet verbose mode"
and doc_version = "\t\tThe version of the compiler"
and doc_print_types = "\t\t\tPrint types"
and doc_include = "<dir>\t\tAdd <dir> to the list of include directories"
and doc_stdlib = "<dir>\t\tDirectory for the standard library"
and doc_object_file = "\t\tOnly generate a .epo object file"
and doc_sim = "<node>\t\tCreate simulation for node <node>"
and doc_hepts = "\t\tSimulation for hepts (graphical simulator)"
and doc_locate_stdlib = "\t\tLocate standard libray"
and doc_no_pervasives = "\tDo not load the pervasives module"
and doc_flatten = "\t\tInline everything."
and doc_target =
  "<lang>\tGenerate code in language <lang>\n\t\t\t(with <lang>=c,"
  ^ " java or z3z)"
and doc_full_type_info = "\t\t\tPrint full type information"
and doc_full_name = "\t\t\tPrint full variable name information"
and doc_target_path =
  "<path>\tGenerated files will be placed in <path>\n\t\t\t(the directory is"
  ^ " cleaned)"
and doc_nocaus = "\t\tDisable causality analysis"
and doc_noinit = "\t\tDisable initialization analysis"
and doc_assert = "<node>\t\tInsert run-time assertions for boolean node <node>"
and doc_inline = "<node>\t\tInline node <node>"
and doc_itfusion = "\t\tEnable iterator fusion."
and doc_tomato = "\t\tEnable automata minimization."
and doc_java_queue_size = "\t\tSet the input queue size for async nodes, 0 means threadPool."
