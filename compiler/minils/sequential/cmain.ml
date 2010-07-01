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
open Modules
open Signature
open C
open Cgen
open Location
open Printf

(** {1 Main C function generation} *)

(* Unique names for C variables handling step counts. *)
let step_counter = Ident.fresh "step_c"
and max_step = Ident.fresh "step_max"

let assert_node_res cd =
  if List.length cd.step.inp > 0 then
    (Printf.eprintf "Cannot generate run-time check for node %s with inputs.\n"
       cd.cl_id;
     exit 1);
  if (match cd.step.out with
        | [{ v_type = Tbool; }] -> false
        | _ -> true) then
    (Printf.eprintf
       "Cannot generate run-time check for node %s with non-boolean output.\n"
       cd.cl_id;
     exit 1);
  let mem = (name (Ident.fresh ("mem_for_" ^ cd.cl_id)),
             Cty_id (cd.cl_id ^ "_mem")) in
  let reset_i =
    Cfun_call (cd.cl_id ^ "_reset", [Caddrof (Cvar (fst mem))]) in
  let step_i =
    (*
      if (!step()) {
        printf("Node $node failed at step %d.\n", step_count);
        return 1;
      }
    *)
    Cif (Cuop ("!", Cfun_call (cd.cl_id ^ "_step", [Caddrof (Cvar (fst mem))])),
         [Csexpr (Cfun_call ("printf",
                             [Cconst (Cstrlit ("Node \\\"" ^ cd.cl_id
                                               ^ "\\\" failed at step %d.\\n"));
                              Clhs (Cvar (name step_counter))]));
          Creturn (Cconst (Ccint 1))],
         []) in
  (mem, Csexpr reset_i, step_i);;

(** [main_def_of_class_def cd] returns a [(var_list, rst_i, step_i)] where
    [var_list] (resp. [rst_i] and [step_i]) is a list of variables (resp. of
    statements) needed for a main() function calling [cd]. *)
(* TODO: refactor into something more readable. *)
let main_def_of_class_def cd =
  let format_for_type ty = match ty with
    | Tarray _ -> assert false
    | Tint | Tbool -> "%d"
    | Tfloat -> "%f"
    | Tid ((Name sid) | Modname { id = sid }) -> "%s" in

  (** Does reading type [ty] need a buffer? When it is the case,
      [need_buf_for_ty] also returns the type's name. *)
  let need_buf_for_ty ty = match ty with
    | Tarray _ -> assert false
    | Tint | Tfloat | Tbool -> None
    | Tid (Name sid | Modname { id = sid; }) -> Some sid in

  (** Generates scanf statements. *)
  let rec read_lhs_of_ty lhs ty = match ty with
    | Tarray (ty, n) ->
        let iter_var = Ident.name (Ident.fresh "i") in
        let lhs = Carray (lhs, Clhs (Cvar iter_var)) in
        let (reads, bufs) = read_lhs_of_ty lhs ty in
        ([Cfor (iter_var, 0, n, reads)], bufs)
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
        (Cfor (iter_var, 0, n, [reads]), bufs)
    | _ ->
        let varn = Ident.name (Ident.fresh "buf") in
        let format_s = format_for_type ty in
        let nbuf_opt = need_buf_for_ty ty in
        let ep = match nbuf_opt with
          | None -> [Clhs lhs]
          | Some sid -> [Cfun_call ("string_of_" ^ sid,
                                    [Clhs lhs;
                                     Clhs (Cvar varn)])] in
        (Csexpr (Cfun_call ("printf",
                            Cconst (Cstrlit ("=> " ^format_s ^ "\\t"))
                            :: ep)),
         match nbuf_opt with
           | None -> []
           | Some id -> [(varn, Cty_arr (20, Cty_char))]) in

  let (scanf_calls, scanf_decls) =
    let read_lhs_of_ty_for_vd vd =
      read_lhs_of_ty (Cvar (Ident.name vd.v_ident)) vd.v_type in
    split (map read_lhs_of_ty_for_vd cd.step.inp) in

  let (printf_calls, printf_decls) =
    let write_lhs_of_ty_for_vd vd = match cd.step.out with
      | [{ v_type = Tarray _; }] ->
          write_lhs_of_ty (Cfield (Cvar "mem", name vd.v_ident)) vd.v_type
      | [_] -> write_lhs_of_ty (Cvar "res") vd.v_type
      | _ ->
          write_lhs_of_ty (Cfield (Cvar "mem", name vd.v_ident)) vd.v_type in
    split (map write_lhs_of_ty_for_vd cd.step.out) in

  let cinp = cvarlist_of_ovarlist cd.step.inp in
  let cout = match cd.step.out with
    | [{ v_type = Tarray _; }] -> []
    | [vd] -> let vty = ctype_of_otype vd.v_type in [("res", vty)]
    | _ -> [] in
  let varlist =
    ("mem", Cty_id (cd.cl_id ^ "_mem"))
    :: cinp
    @ cout
    @ concat scanf_decls
    @ concat printf_decls in

  (** The main function loops (while (1) { ... }) reading arguments for our node
      and prints the results. *)
  let step_l =
    let funcall =
      let args =
        map (fun vd -> Clhs (Cvar (name vd.v_ident))) cd.step.inp
        @ [Caddrof (Cvar "mem")] in
      Cfun_call (cd.cl_id ^ "_step", args) in
    concat scanf_calls
      (* Our function returns something only when the node has exactly one
         scalar output. *)
    @ ([match cd.step.out with
          | [{ v_type = Tarray _; }] -> Csexpr funcall
          | [_] -> Caffect (Cvar "res", funcall)
          | _ -> Csexpr funcall])
    @ printf_calls
    @ [Csexpr (Cfun_call ("puts", [Cconst (Cstrlit "")]));
       Csexpr (Cfun_call ("fflush", [Clhs (Cvar "stdout")]))] in

  (** Do not forget to initialize memory via reset. *)
  let rst_i =
    Csexpr (Cfun_call (cd.cl_id ^ "_reset", [Caddrof (Cvar "mem")])) in

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
                  :: body)
        ];
    }
  }

let mk_main p = match (!Misc.simulation_node, !Misc.assert_nodes) with
  | (None, []) -> []
  | (_, n_names) ->
      let find_class n =
        try List.find (fun cd -> cd.cl_id = n) p.o_defs
        with Not_found ->
          Printf.eprintf "Unknown node %s.\n" n;
          exit 1 in

      let a_classes = List.map find_class n_names in

      let (var_l, res_l, step_l) =
        let add cd (var_l, res_l, step_l) =
          let (var, res, step) = assert_node_res cd in
          (var :: var_l, res :: res_l, step :: step_l) in
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
