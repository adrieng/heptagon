(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Format
open List
open Misc
open Names
open Ident
open Obc
open Types
open Modules
open Signature
open C
open Cgen
open Location
open Printf
open Compiler_utils

(** {1 Main C function generation} *)

(* Unique names for C variables handling step counts. *)
let step_counter = Ident.fresh "step_c"
and max_step = Ident.fresh "step_max"

let assert_node_res cd =
  let stepm = find_step_method cd in
  if List.length stepm.m_inputs > 0 then
    (Printf.eprintf "Cannot generate run-time check for node %s with inputs.\n"
       cd.cd_name;
     exit 1);
  if (match stepm.m_outputs with
        | [{ v_type = Tid nbool; }] when nbool = Initial.pbool -> false
        | _ -> true) then
    (Printf.eprintf
       "Cannot generate run-time check for node %s with non-boolean output.\n"
       cd.cd_name;
     exit 1);
  let mem =
    (name (Ident.fresh ("mem_for_" ^ cd.cd_name)), Cty_id (cd.cd_name ^ "_mem"))
  and out =
    (name (Ident.fresh ("out_for_" ^ cd.cd_name)), Cty_id (cd.cd_name ^ "_out")) in
  let reset_i =
    Cfun_call (cd.cd_name ^ "_reset", [Caddrof (Cvar (fst mem))]) in
  let step_i =
    (*
      step(&out, &mem);
      if (!out.proper_name) {
        printf("Node $node failed at step %d.\n", step_count);
        return 1;
      }
    *)
    let outn = Ident.name ((List.hd stepm.m_outputs).v_ident) in
    Csblock
      { var_decls = [];
        block_body =
          [
            Csexpr (Cfun_call (cd.cd_name ^ "_step",
                               [Caddrof (Cvar (fst out));
                                Caddrof (Cvar (fst mem))]));
            Cif (Cuop ("!", Clhs (Cfield (Cvar (fst out), outn))),
                 [Csexpr (Cfun_call ("printf",
                                     [Cconst (Cstrlit ("Node \\\"" ^ cd.cd_name
                                                       ^ "\\\" failed at step" ^
                                                       " %d.\\n"));
                                      Clhs (Cvar (name step_counter))]));
                  Creturn (Cconst (Ccint 1))],
                 []);
          ];
      } in
  ([out; mem], Csexpr reset_i, step_i);;

(** [main_def_of_class_def cd] returns a [(var_list, rst_i, step_i)] where
    [var_list] (resp. [rst_i] and [step_i]) is a list of variables (resp. of
    statements) needed for a main() function calling [cd]. *)
(* TODO: refactor into something more readable. *)
let main_def_of_class_def cd =
  let format_for_type ty = match ty with
    | Tarray _ -> assert false
    | Types.Tid id when id = Initial.pfloat -> "%f"
    | Types.Tid id when id = Initial.pint -> "%d"
    | Types.Tid id when id = Initial.pbool -> "%d"
    | Tid ((Name sid) | Modname { id = sid }) -> "%s" in

  (** Does reading type [ty] need a buffer? When it is the case,
      [need_buf_for_ty] also returns the type's name. *)
  let need_buf_for_ty ty = match ty with
    | Tarray _ -> assert false
    | Types.Tid id when id = Initial.pfloat -> None
    | Types.Tid id when id = Initial.pint -> None
    | Types.Tid id when id = Initial.pbool -> None
    | Tid (Name sid | Modname { id = sid; }) -> Some sid in

  let cprint_string s = Csexpr (Cfun_call ("printf", [Cconst (Cstrlit s)])) in

  (** Generates scanf statements. *)
  let rec read_lhs_of_ty lhs ty = match ty with
    | Tarray (ty, n) ->
        let iter_var = Ident.name (Ident.fresh "i") in
        let lhs = Carray (lhs, Clhs (Cvar iter_var)) in
        let (reads, bufs) = read_lhs_of_ty lhs ty in
        ([Cfor (iter_var, 0, int_of_static_exp n, reads)], bufs)
    | _ ->
        let rec mk_prompt lhs = match lhs with
          | Cvar vn -> (vn, [])
          | Carray (lhs, cvn) ->
              let (vn, args) = mk_prompt lhs in
              (vn ^ "[%d]", cvn :: args)
          | _ -> assert false in
        let (prompt, args_format_s) = mk_prompt lhs in
        let scan_exp =
          let printf_s = Printf.sprintf "%s ? " prompt in
          let format_s = format_for_type ty in
          Csblock { var_decls = [];
                    block_body = [
                      Csexpr (Cfun_call ("printf",
                                         Cconst (Cstrlit printf_s)
                                         :: args_format_s));
                      Csexpr (Cfun_call ("scanf",
                                         [Cconst (Cstrlit format_s);
                                          Caddrof lhs])); ]; } in
        match need_buf_for_ty ty with
          | None -> ([scan_exp], [])
          | Some tyn ->
              let varn = Ident.name (Ident.fresh "buf") in
              ([scan_exp;
                Csexpr (Cfun_call (tyn ^ "_of_string",
                                   [Clhs (Cvar varn)]))],
               [(varn, Cty_arr (20, Cty_char))]) in

  (** Generates printf statements and buffer declarations needed for printing
      resulting values of enum types. *)
  let rec write_lhs_of_ty lhs ty = match ty with
    | Tarray (ty, n) ->
        let iter_var = Ident.name (Ident.fresh "i") in
        let lhs = Carray (lhs, Clhs (Cvar iter_var)) in
        let (reads, bufs) = write_lhs_of_ty lhs ty in
        ([cprint_string "[ ";
          Cfor (iter_var, 0, int_of_static_exp n, reads);
          cprint_string "]"], bufs)
    | _ ->
        let varn = Ident.name (Ident.fresh "buf") in
        let format_s = format_for_type ty in
        let nbuf_opt = need_buf_for_ty ty in
        let ep = match nbuf_opt with
          | None -> [Clhs lhs]
          | Some sid -> [Cfun_call ("string_of_" ^ sid,
                                    [Clhs lhs;
                                     Clhs (Cvar varn)])] in
        ([Csexpr (Cfun_call ("printf",
                             Cconst (Cstrlit (format_s ^ " "))
                             :: ep))],
         match nbuf_opt with
           | None -> []
           | Some id -> [(varn, Cty_arr (20, Cty_char))]) in

  let stepm = find_step_method cd in
  let (scanf_calls, scanf_decls) =
    let read_lhs_of_ty_for_vd vd =
      read_lhs_of_ty (Cvar (Ident.name vd.v_ident)) vd.v_type in
    split (map read_lhs_of_ty_for_vd stepm.m_inputs) in

  let (printf_calls, printf_decls) =
    let write_lhs_of_ty_for_vd vd =
      let (stm, vars) =
        write_lhs_of_ty (Cfield (Cvar "res", name vd.v_ident)) vd.v_type in
      (cprint_string "=> " :: stm, vars) in
    split (map write_lhs_of_ty_for_vd stepm.m_outputs) in
  let printf_calls = List.concat printf_calls in

  let cinp = cvarlist_of_ovarlist stepm.m_inputs in
  let cout = ["res", (Cty_id (cd.cd_name ^ "_out"))] in

  let varlist =
    ("mem", Cty_id (cd.cd_name ^ "_mem"))
    :: cinp
    @ cout
    @ concat scanf_decls
    @ concat printf_decls in

  (** The main function loops (while (1) { ... }) reading arguments for our node
      and prints the results. *)
  let step_l =
    let funcall =
      let args =
        map (fun vd -> Clhs (Cvar (name vd.v_ident))) stepm.m_inputs
        @ [Caddrof (Cvar "res"); Caddrof (Cvar "mem")] in
      Cfun_call (cd.cd_name ^ "_step", args) in
    concat scanf_calls
    @ [Csexpr funcall]
    @ printf_calls
    @ [Csexpr (Cfun_call ("puts", [Cconst (Cstrlit "")]));
       Csexpr (Cfun_call ("fflush", [Clhs (Cvar "stdout")]))] in

  (** Do not forget to initialize memory via reset. *)
  let rst_i =
    Csexpr (Cfun_call (cd.cd_name ^ "_reset", [Caddrof (Cvar "mem")])) in

  (varlist, rst_i, step_l)

(** [main_skel var_list prologue body] generates a C main() function using the
    variable list [var_list], prologue [prologue] and loop body [body]. *)
let main_skel var_list prologue body =
  Cfundef {
    f_name = "main";
    f_retty = Cty_int;
    f_args = [("argc", Cty_int); ("argv", Cty_ptr (Cty_ptr Cty_char))];
    f_body = {
      var_decls =
        (name step_counter, Cty_int) :: (name max_step, Cty_int) :: var_list;
      block_body =
        [
          (*
            step_count = 0;
            max_step = 0;
            if (argc == 2)
              max_step = atoi(argv[1]);
          *)
          Caffect (Cvar (name step_counter), Cconst (Ccint 0));
          Caffect (Cvar (name max_step), Cconst (Ccint 0));
          Cif (Cbop ("==", Clhs (Cvar "argc"), Cconst (Ccint 2)),
               [Caffect (Cvar (name max_step),
                         Cfun_call ("atoi",
                                    [Clhs (Carray (Cvar "argv",
                                                   Cconst (Ccint 1)))]))], []);
        ]
        @ prologue
          (* while (!max_step || step_c < max_step) *)
        @ [
          Cwhile (Cbop ("||",
                        Cuop ("!", Clhs (Cvar (name max_step))),
                        Cbop ("<",
                              Clhs (Cvar (name step_counter)),
                              Clhs (Cvar (name max_step)))),
                  (* step_counter = step_counter + 1; *)
                  Caffect (Cvar (name step_counter),
                           Cbop ("+",
                                 Clhs (Cvar (name step_counter)),
                                 Cconst (Ccint 1)))
                  :: body);
          Creturn (Cconst (Ccint 0));
        ];
    }
  }

let mk_main p = match (!Misc.simulation_node, !Misc.assert_nodes) with
  | (None, []) -> []
  | (_, n_names) ->
      let find_class n =
        try List.find (fun cd -> cd.cd_name = n) p.p_defs
        with Not_found ->
          Printf.eprintf "Unknown node %s.\n" n;
          exit 1 in

      let a_classes = List.map find_class n_names in

      let (var_l, res_l, step_l) =
        let add cd (var_l, res_l, step_l) =
          let (var, res, step) = assert_node_res cd in
          (var @ var_l, res :: res_l, step :: step_l) in
        List.fold_right add a_classes ([], [], []) in

      let (deps, var_l, res_l, step_l) =
        (match !Misc.simulation_node with
           | None -> (n_names, var_l, res_l, step_l)
           | Some n ->
               let (nvar_l, res, nstep_l) =
                 main_def_of_class_def (find_class n) in
               (n :: n_names, nvar_l @ var_l,
                res :: res_l, nstep_l @ step_l)) in

      [("_main.c", Csource [main_skel var_l res_l step_l]);
       ("_main.h", Cheader (deps, []))];
;;


(******************************)

let translate name prog =
  let modname = (Filename.basename name) in
  global_name := String.capitalize modname;
  (global_file_header modname prog) :: (mk_main prog)
  @ (cfile_list_of_oprog modname prog)

let program p =
  let filename = filename_of_name (cname_of_name p.p_modname) in
  let dirname = build_path (filename ^ "_c") in
  let dir = clean_dir dirname in
  let c_ast = translate filename p in
    C.output dir c_ast
