(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

let generate_targets p =
   (* Producing Object-based code *)
  let o = Translate.program p in
    if !verbose then comment "Translation into Object-based code";
    Obc.Printer.print obc o;

    let pp = Obc.Printer.print stdout in
      if !verbose then pp o;

    (* Translation into dataflow and sequential languages *)
    targets filename p o !target_languages

let parse_implementation lexbuf =
  parse Parser.program Lexer.token lexbuf

let compile_impl modname filename = 
  (* input and output files *)
  (* input and output files *)
  let mls_name = filename ^ ".mls"
  and mls_norm_name = filename ^ "_norm.mls"
  and obc_name = filename ^ ".obc" in

  let mlsc = open_out mls_name
  and mlsnc = open_out mls_norm_name
  and obc = open_out obc_name in

  let close_all_files () =
    close_out mlsc;
    close_out obc;
    close_out mlsnc
  in

    try
      init_compiler modname source_name ic;
        
      (* Parsing of the file *)
      let lexbuf = Lexing.from_channel ic in
      let p = parse_implementation lexbuf in

      (* Convert the parse tree to Heptagon AST *)
      let p = Scoping.translate_program p in
        if !verbose
        then begin
          comment "Parsing";
          pp p
        end;

        (* Call the compiler*)
        Hept_compiler.compile_impl pp p;

        if !verbose
        then begin
          comment "Checking"
        end;    
        close_all_files ()

    with x -> close_all_files (); raise x  

let compile file =
  if Filename.check_suffix file ".mls" then
    let filename = Filename.chop_suffix file ".ept" in
    let modname = String.capitalize(Filename.basename filename) in
      compile_impl modname filename
  else
    raise (Arg.Bad ("Unknow file type: " ^ file))

let errmsg = "Options are:"

let main () =
  try
    Arg.parse
      [
        "-v",Arg.Set verbose, doc_verbose;
        "-version", Arg.Unit show_version, doc_version;
        "-i", Arg.Set print_types, doc_print_types;
        "-I", Arg.String add_include, doc_include;
        "-where", Arg.Unit locate_stdlib, doc_locate_stdlib;
        "-stdlib", Arg.String set_stdlib, doc_stdlib;
        "-s", Arg.String set_simulation_node, doc_sim;
        "-nopervasives", Arg.Unit set_no_pervasives, doc_no_pervasives;
        "-target", Arg.String add_target_language, doc_target;
        "-targetpath", Arg.String set_target_path, doc_target_path;
	      "-noinit", Arg.Clear init, doc_noinit;
        "-fti", Arg.Set full_type_info, doc_full_type_info;
      ]
      compile
      errmsg;
  with
    | Misc.Error -> exit 2;;

main ()
