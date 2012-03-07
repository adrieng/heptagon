(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Compiler_utils
open Compiler_options
open Obc
open Minils
open Misc

(** Definition of a target. A target starts either from
    dataflow code (ie Minils) or sequential code (ie Obc),
    with or without static parameters *)
type program_target =
  | Obc of (Obc.program -> unit)
  | Obc_no_params of (Obc.program -> unit)
  | Minils of (Minils.program -> unit)
  | Minils_no_params of (Minils.program -> unit)

type interface_target =
  | IObc of (Obc.interface -> unit)
  | IMinils of (Minils.interface -> unit)

type target =
    { t_name : string;
      t_program : program_target;
      t_interface : interface_target;
      t_load_conf : unit -> unit }

let no_conf () = ()

let mk_target ?(interface=IMinils ignore) ?(load_conf = no_conf) name pt =
  { t_name = name; t_program = pt;
    t_interface = interface; t_load_conf = load_conf }

(** Writes a .epo file for program [p]. *)
let write_object_file p =
  let filename = (Names.modul_to_string p.Minils.p_modname)^".epo" in
  let epoc = open_out_bin filename in
    output_value epoc p;
    close_out epoc;
    comment "Generating of object file"

(** Writes a .obc file for program [p]. *)
let write_obc_file p =
  let obc_name = (Names.modul_to_string p.Obc.p_modname)^".obc" in
  let obc = open_out obc_name in
    do_silent_pass "Obc serialization" (Obc_printer.print obc) p;
    close_out obc;
    comment "Generation of Obc code"

let targets =
  [ mk_target ~interface:(IObc Cmain.interface) "c" (Obc_no_params Cmain.program);
    (* TODO callgraph only when high order stuff *)
    mk_target ~load_conf:(Java_main.load_conf) "java" (Obc_no_params Java_main.program);
    mk_target ~load_conf:java_conf "java" (Obc Java_main.program);
    mk_target "z3z" (Minils_no_params Sigalimain.program);
    mk_target "obc" (Obc write_obc_file);
    mk_target "obc_np" (Obc_no_params write_obc_file);
    mk_target "epo" (Minils write_object_file) ]

let find_target s =
  try
    List.find (fun t -> t.t_name = s) targets
  with
      Not_found -> language_error s; raise Errors.Error

let generate_target p s =
(*  let print_unfolded p_list =
    comment "Unfolding";
    if !Compiler_options.verbose
    then List.iter (Mls_printer.print stderr) p_list in *)
  let target = (find_target s).t_program in
  let callgraph p = do_silent_pass "Callgraph" Callgraph.program p in
  let mls2obc p = do_silent_pass "Translation into MiniLS" Mls2obc.program p in
  let mls2obc_list p_l = do_silent_pass "Translation into MiniLS" (List.map Mls2obc.program) p_l in
  match target with
    | Minils convert_fun ->
        do_silent_pass "Code generation from MiniLS" convert_fun p
    | Obc convert_fun ->
        let o = mls2obc p in
        let o = do_pass "Convert to Obc" Mls2obc.program p pp in
        let o = Obc_compiler.compile_program o in
        do_silent_pass "Code generation from Obc" convert_fun o
    | Minils_no_params convert_fun ->
        let p_list = callgraph p in
        do_silent_pass "Code generation from Obc (w/o params)" (List.iter convert_fun) p_list
    | Obc_no_params convert_fun ->
        let p_list = callgraph p in
        let o_list = mls2obc_list p_list in
        let o_list = List.map Obc_compiler.compile_program o_list in
        do_silent_pass "Code generation from Obc (w/o params)"         List.iter convert_fun o_list

let generate_interface i s =
  let target = (find_target s).t_interface  in
  match target with
    | IObc convert_fun ->
      let o = do_silent_pass "Translation into Obc (interfaces)" Mls2obc.interface i in
      convert_fun o
    | IMinils convert_fun -> convert_fun i

let load_conf () =
  List.iter (fun s -> (find_target s).t_load_conf ()) !target_languages;
  try
    check_options ()
  with Arg.Bad m -> raise (Arg.Bad ("After loading target configurations: "^m))

(** Translation into dataflow and sequential languages, defaults to obc. *)
let program p =
  let targets = match !target_languages with
    | [] -> ["obc"] (* by default, generate obc file *)
    | l -> l in
  let targets = if !create_object_file then "epo"::targets else targets in
  List.iter (generate_target p) targets

let interface i =
  let targets = match !target_languages with
    | [] -> [] (* by default, generate obc file *)
    | l -> l in
  List.iter (generate_interface i) targets
