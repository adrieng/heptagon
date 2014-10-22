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
  (* "ctrln", `Ctrln; "cn", `Ctrln; *)
  "ctrlf", `Ctrlf; "cf", `Ctrlf;
  (* "ctrlr", `Ctrlr; "cr", `Ctrlr; *)
]

(** Name of official input types as understood by the tool. *)
let ityps = List.map fst ityps_alist

let set_input_type r t =
  try r := Some (List.assoc t ityps_alist) with
    | Not_found -> raise (Arg.Bad (asprintf "Unknown input file type: `%s'" t))

let inputs = ref []
let output = ref ""
let input_type = ref None

let anon x = inputs := x :: !inputs
let options =
  [
    "-v",Arg.Set verbose, doc_verbose;
    "-version", Arg.Unit show_version, doc_version;
    "-i", Arg.String anon, "<file> ";
    "-input-type", Arg.Symbol (ityps, set_input_type input_type), "Input file type";
    "--input-type", Arg.Symbol (ityps, set_input_type input_type), "";
    "-o", Arg.Set_string output, "<file> ";
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
      let filename = asprintf "%s.%s" basename ext in
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
    CtrlNbac.Symb.reset ();
    let s, n, msgs = parse ?filename () in
    report_msgs ?filename msgs;
    s, n
  with
    | CtrlNbac.Parser.Error (n, msgs) -> abort ?filename n msgs

(* -------------------------------------------------------------------------- *)

let handle_ctrlf ?filename mk_oc =
  let name, func = parse_input ?filename CtrlNbac.Parser.Unsafe.parse_func in
  let name = match name with None -> "ctrlr" | Some n -> n ^"_ctrlr" in
  let prog = CtrlNbacAsEpt.gen_func ~module_name:name func in
  let oc, close = mk_oc.out_exec "ept" in
  Hept_printer.print oc prog;
  close ()

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

let handle_input_file ?ityp filename =
  let ityp, mk_oc = match ityp with
    | None -> guesstyp_n_output filename
    | Some ityp -> ityp, snd (guesstyp_n_output filename)
  in
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
  Arg.parse options anon errmsg;
  match List.rev !inputs with
    | [] -> handle_input_stream !input_type
    | lst -> List.iter (handle_input_file ?ityp:!input_type) lst

(* -------------------------------------------------------------------------- *)
(** Launch the [main] *)
let _ =
  try
    main ()
  with
    | Errors.Error -> error "aborted."; exit 2
    | Arg.Bad s | Sys_error s -> error "%s" s; exit 2
