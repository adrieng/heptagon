open Format
open Filename
open CtrlNbac
open Compiler_utils
open Compiler_options

(* -------------------------------------------------------------------------- *)

let report_msgs ?filename =
  let report_msg = Parser.Reporting.report_msg ?filename err_formatter in
  List.iter begin function
    | #CtrlNbac.Parser.msg as msg -> report_msg msg
    | `TError info -> report_msg (`MError info)
  end

let abort ?filename n msgs =
  report_msgs ?filename msgs;
  error "Aborting due to errors in %s" n;
  exit 1

(* -------------------------------------------------------------------------- *)

(** File extensions officially understood by the tool, with associated input
    types. *)
let ityps_alist = [
  "ctrlf", `Ctrlf; "cf", `Ctrlf;
  "ctrls", `Ctrlf; "cs", `Ctrlf; (* No need to discriminate between weaved and
                                    split functions (for now). *)
]

(** name of official input types as understood by the tool. *)
let ityps = List.map fst ityps_alist

let set_input_type r t =
  try r := Some (List.assoc t ityps_alist) with
    | Not_found -> raise (Arg.Bad (asprintf "Unknown input file type: `%s'" t))

let inputs = ref []
let output = ref ""
let input_type = ref None
let node = ref ""
let modul = ref ""

exception Help
let usage = "Usage: ctrl2ept [options] { [-i] <filename> | -n <node> } \
                    [ -- { <filename> } ]"
let print_vers () =
  fprintf err_formatter "ctrl2ept, version %s (compiled on %s)@." version date;
  exit 0
let anon x = inputs := x :: !inputs
let it = Arg.Symbol (ityps, set_input_type input_type)
let options = Arg.align
  [
    "-i", Arg.String anon, "<file> Input file (`-' means standard input)";
    "-input-type", it, " Input file type";
    "--input-type", it, "";
    "-o", Arg.Set_string output, "<file> Select output file (`-' means \
                                  standard output)";
    "-n", Arg.Set_string node, "<node> Select base input node";
    "-m", Arg.Set_string modul, "<Module> Select base input module";
    "--", Arg.Rest anon, " Treat all remaining arguments as input files";
    "-where", Arg.Unit locate_stdlib, doc_locate_stdlib;
    "-stdlib", Arg.String set_stdlib, doc_stdlib;
    "-v",Arg.Set verbose, " Set verbose mode";
    "-version", Arg.Unit print_vers, " Print the version of the compiler";
    "--version", Arg.Unit print_vers, "";
    "-h", Arg.Unit (fun _ -> raise Help), "";
  ]

(* -------------------------------------------------------------------------- *)

type out =
    {
      out_mult: bool;            (* Are multiple calls to `out_exec' allowed? *)
      out_exec: string -> out_channel * (unit -> unit);           (* oc * close *)
    }

(* --- *)

let mk_oc basename =
  {
    out_exec = (fun ext ->
      let filename = asprintf "%s%s" basename ext in
      let oc = open_out filename in
      info "Outputting into `%s'…" filename;
      oc, (fun () -> flush oc; close_out oc));
    out_mult = true;
  }

let mk_oc' filename =
  {
    out_exec = (fun _ ->
      let oc = open_out filename in
      info "Outputting into `%s'…" filename;
      oc, (fun () -> flush oc; close_out oc));
    out_mult = false;
  }

let mk_std_oc =
  {
    out_exec = (fun _ ->
      info "Outputting onto standard output…";
      stdout, (fun () -> flush stdout));
    out_mult = true;
  }

(* --- *)

(** Parses the given input file. *)
let parse_input ?filename (parse: ?filename:string -> _) =
  try
    let s, n, msgs = parse ?filename () in
    report_msgs ?filename msgs;
    s, n
  with
    | CtrlNbac.Parser.Error (n, msgs) -> abort ?filename n msgs

(* -------------------------------------------------------------------------- *)

exception Error of string

let suppress_typedecl ?mo prog =
  let open Heptagon in
  let p_desc =
    List.fold_left
      (fun acc d -> match d with
                      Ptype _ -> acc
                    | _ -> d::acc)
      []
      prog.p_desc in
  let p_opened =
    match mo with
      None -> prog.p_opened
    | Some m -> m :: prog.p_opened in
  { prog with
    p_opened;
    p_desc = List.rev p_desc;
  }

let parse_n_gen_ept_node ?filename ?node_name ?node_sig ?typ_symbs () =
  let name, func = parse_input ?filename CtrlNbac.Parser.Unsafe.parse_func in
  let node_name = match node_name with Some n -> n
    | None -> match name with None -> assert false
        | Some n -> Names.local_qn (n ^ "_ctrlr")
  in
  name, CtrlNbacAsEpt.gen_func ?typ_symbs ~node_name ?node_sig func

let handle_ctrlf ?filename mk_oc =
  let _, decls = parse_n_gen_ept_node ?filename () in
  let prog = CtrlNbacAsEpt.create_prog Names.LocalModule in    (* don't care? *)
  let prog = List.fold_right CtrlNbacAsEpt.add_to_prog decls prog in
  let prog = suppress_typedecl prog in
  let oc, close = mk_oc.out_exec "ept" in
  Hept_printer.print oc prog;
  close ()

(* -------------------------------------------------------------------------- *)

let parse_nodename nn = try Names.qualname_of_string nn with
  | Exit -> raise (Error (sprintf "Invalid node name: `%s'" nn))

let output_prog prog modul =
  Modules.select modul;
  let filename = String.uncapitalize_ascii (Names.modul_to_string modul) ^ ".ept" in
  let oc = open_out filename in
  info "Outputting into `%s'…" filename;
  Hept_printer.print oc prog;
  close_out oc

let input_function prog typ_symbs filename node_name node_sig =
  info "Reading function from `%s'…" filename;
  let _, decls = parse_n_gen_ept_node ~filename ~node_name ~node_sig ~typ_symbs () in
  (* XXX: check types are also in signature? actually, we only use the types
     declared in the signature instead, as long as the controller synthesis tool
     does not introduce new types. *)
  List.fold_right CtrlNbacAsEpt.add_to_prog decls prog

let try_ctrlf typ_symbs nn prog =
  let node_name = Ctrln_utils.controller_node nn in
  if Modules.check_value node_name then
    let filename = Ctrln_utils.ctrlf_for_node nn in
    let node_sig = Modules.find_value node_name in
    input_function prog typ_symbs filename node_name node_sig
  else
    raise Exit

let try_ctrls typ_symbs nn prog =
  let rec try_ctrls num prog =
    let node_name = Ctrln_utils.controller_node ~num nn in
    if Modules.check_value node_name then
      let filename = Ctrln_utils.ctrls_for_node nn num in
      if num = 0 && not (Sys.file_exists filename) then
        raise Exit;                                                  (* abort *)
      let node_sig = Modules.find_value node_name in
      let prog = input_function prog typ_symbs filename node_name node_sig in
      try_ctrls (succ num) prog
    else
      prog
  in
  try_ctrls 0 prog

let handle_node arg =
  let nn = parse_nodename arg in

  let mo = Names.modul nn in
  if mo = Names.Pervasives || mo = Names.LocalModule then
    raise (Error (sprintf "Invalid node specification: `%s'." arg));

  Modules.open_module Names.Pervasives;
  info "Loading module of controllers for node %s…" (Names.fullname nn);
  let om = Ctrln_utils.controller_modul mo in
  info "Translating type declarations of module %s…" (Names.modul_to_string om);
  let _typs, typ_symbs = CtrlNbacAsEpt.decl_typs_from_module_itf mo in
  let prog = CtrlNbacAsEpt.create_prog ~open_modul:[mo] om in
  (* let prog = List.fold_right CtrlNbacAsEpt.add_to_prog typs prog in *)
  let prog = try try_ctrls typ_symbs nn prog with
             | Exit ->
                try try_ctrlf typ_symbs nn prog with
                  Exit ->
                  raise (Error "Unable to load any controller function.")
  in
  output_prog prog om

let handle_module modname =
  let mo = Names.modul_of_string modname in
  if mo = Names.Pervasives || mo = Names.LocalModule then
    raise (Error (sprintf "Invalid module specification: `%s'." modname));
  Modules.open_module Names.Pervasives;
  Modules.open_module mo;
  Modules.select mo;
  let curmod = Modules.current_module () in
  info "Loading module of controllers for module %s…" (Names.modul_to_string mo);
  let om = Ctrln_utils.controller_modul mo in
  info "Translating type declarations of module %s…" (Names.modul_to_string om);
  let _typs, typ_symbs = CtrlNbacAsEpt.decl_typs_from_module_itf mo in
  let prog = CtrlNbacAsEpt.create_prog ~open_modul:[mo] om in
  let prog =
    Names.NamesEnv.fold
      (fun nodename _node prog ->
       info "Handling function %s…" nodename;
       let nn = Names.{ qual = mo; name = nodename } in
       try try_ctrls typ_symbs nn prog with
       | Exit ->
          try try_ctrlf typ_symbs nn prog with
            Exit -> prog)
      curmod.Modules.m_values prog in
  output_prog prog om

(* -------------------------------------------------------------------------- *)

let ityp_name_n_handle = function
  (* | `Ctrln -> "node", handle_ctrln *)
  | `Ctrlf -> "function", handle_ctrlf
  (* | `Ctrlr -> "predicate", handle_ctrlr *)

let guesstyp_n_output filename =
  try
    let typ = match !input_type with
      | Some t -> t
      | None -> snd (List.find (fun (suff, _) -> check_suffix filename suff)
                      ityps_alist)
    in
    let basename_extra = match typ with
      | `Ctrlf -> "_ctrlr"
    in
    typ,
    (match !output with
      | "-" -> mk_std_oc
      | "" -> (try chop_extension filename ^ basename_extra |> mk_oc with
          | Invalid_argument _ when filename <> "" -> mk_oc filename
          | Invalid_argument _ -> mk_std_oc)
      | o -> mk_oc' o)
  with
    | Not_found ->
        raise (Arg.Bad (sprintf "Cannot guess input type of `%s'" filename))

let handle_input_file filename =
  let ityp, mk_oc = guesstyp_n_output filename in
  let itypname, handle = ityp_name_n_handle ityp in
  info "Reading %s from `%s'…" itypname filename;
  handle ~filename mk_oc

let handle_input_stream = function
  | None ->
      info "Reading function from standard input…";
      handle_ctrlf mk_std_oc
  | Some ityp ->
      let itypname, handle = ityp_name_n_handle ityp in
      info "Reading %s from standard input…" itypname;
      handle mk_std_oc

(** [main] function to be launched *)
let main () =
  Arg.parse options anon usage;
  match (!modul,!node,List.rev !inputs) with
    | "","",[] -> handle_input_stream !input_type
    | "",n,lst -> (handle_node n; List.iter handle_input_file lst)
    | m,_,lst -> (handle_module m; List.iter handle_input_file lst)

(* -------------------------------------------------------------------------- *)

(* Launch the [main] *)
let _ =
  (* CtrlNbac.Symb.reset (); <- not needed as we have only one input file. *)
  try
    main ()
  with
    | Help -> Arg.usage options usage
    | Errors.Error -> error "aborted."; exit 2
    | Error s | Arg.Bad s | Sys_error s -> error "%s" s; exit 2
