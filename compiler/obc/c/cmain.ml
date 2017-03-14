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

open List
open Names
open Idents
open Obc
open Obc_utils
open Types
open Signature
open C
open Cgen
open Compiler_utils

(** {1 Main C function generation} *)

let _ = Idents.enter_node (Modules.fresh_value "cmain" "main")

let fresh n = Idents.name (Idents.gen_var "cmain" n)

let mk_int i = Cconst (Ccint i)
let mk_float f = Cconst (Ccfloat f)

(* Unique names for C variables handling step counts. *)
let step_counter = fresh "step_c"
and max_step = fresh"step_max"

let assert_node_res cd =
  let stepm = find_step_method cd in
  if List.length stepm.m_inputs > 0 then
    (Format.eprintf "Cannot generate run-time check for node %s with inputs.@."
       (cname_of_qn cd.cd_name);
     exit 1);
  if (match stepm.m_outputs with
        | [{ v_type = Tid nbool; }] when nbool = Initial.pbool -> false
        | _ -> true) then
    (Format.eprintf
       "Cannot generate run-time check for node %s with non-boolean output.@."
       (cname_of_qn cd.cd_name);
     exit 1);
  let name = cname_of_qn cd.cd_name in
  let out =
    (fresh ("out_for_" ^ name),
      Cty_id (qn_append cd.cd_name "_out")) in
  let mem, reset_i =
    if not cd.cd_stateful
    then ([], [])
    else
      let mem =
        (fresh ("mem_for_" ^ name), Cty_id (qn_append cd.cd_name "_mem")) in
      ([mem],
       [Csexpr (Cfun_call (name ^ "_reset", [Caddrof (Cvar (fst mem))]))]) in
  let step_i =
    (*
      step(&out, &mem);
      if (!out.proper_name) {
        printf("Node $node failed at step %d.\n", step_count);
        return 1;
      }
    *)
    let outn = Idents.name ((List.hd stepm.m_outputs).v_ident) in
    Csblock
      { var_decls = [];
        block_body =
          [
            Csexpr (Cfun_call (name ^ "_step",
                               Caddrof (Cvar (fst out))
                               :: (if cd.cd_stateful
                                   then [Caddrof (Cvar (fst (List.hd mem)))]
                                   else [])));
            Cif (Cuop ("!", Cfield (Cvar (fst out), local_qn outn)),
                 [Csexpr (Cfun_call ("fprintf",
                                     [Cvar "stderr";
                                      Cconst (Cstrlit ("Node \""
                                                       ^ (Names.fullname cd.cd_name)
                                                            ^ "\" failed at step" ^
                                                              " %d.\n"));
                                      Cvar step_counter]));
                  Creturn (mk_int 1)],
                 []);
          ];
      } in
  (out :: mem, reset_i, step_i);;

(** [main_def_of_class_def cd] returns a [(var_list, rst_i, step_i)] where
    [var_list] (resp. [rst_i] and [step_i]) is a list of variables (resp. of
    statements) needed for a main() function calling [cd]. *)
let main_def_of_class_def cd =
  let format_for_type ty = match ty with
    | Tarray _ | Tprod _ | Tinvalid -> assert false
    | Types.Tid id when id = Initial.pfloat -> "%f"
    | Types.Tid id when id = Initial.pint -> "%d"
    | Types.Tid id when id = Initial.pbool -> "%d"
    | Tid _ -> "%s"
  in

  (* Does reading type [ty] need a buffer? When it is the case,
     [need_buf_for_ty] also returns the type's name. *)
  let need_buf_for_ty ty = match ty with
    | Tarray _ | Tprod _ | Tinvalid -> assert false
    | Types.Tid id when id = Initial.pfloat -> None
    | Types.Tid id when id = Initial.pint -> None
    | Types.Tid id when id = Initial.pbool -> None
    | Tid tn -> Some (cname_of_qn tn)
  in
  let cprint_string s = Csexpr (Cfun_call ("printf", [Cconst (Cstrlit s)])) in

  (* Generates scanf statements. *)
  let rec read_lhs_of_ty lhs ty =
    match ty with
    | Tarray (ty, n) ->
        let iter_var = fresh "i" in
        let lhs = Carray (lhs, Cvar iter_var) in
        let (reads, bufs) = read_lhs_of_ty lhs ty in
        ([Cfor (iter_var, mk_int 0, cexpr_of_static_exp n, reads)], bufs)
    | (Tid tn) as ty ->
        begin match Modules.find_type tn with
        | Talias ty -> read_lhs_of_ty lhs ty
        | Tstruct field_list ->
            List.fold_left
              (fun (reads,bufs)
                 { Signature.f_name = f_name; Signature.f_type = f_ty} ->
                 let f_lhs = Cfield(lhs,f_name) in
                 let (f_reads,f_bufs) = read_lhs_of_ty f_lhs f_ty in
                 (reads@f_reads),(bufs@f_bufs))
              ([],[])
              field_list
        | _ ->
            let rec mk_prompt lhs = match lhs with
              | Cvar vn -> (vn, [])
              | Carray (lhs, cvn) ->
                  let (vn, args) = mk_prompt lhs in
                  (vn ^ "[%d]", cvn :: args)
              | Cfield (lhs, fn) ->
                  let (vn, args) = mk_prompt lhs in
                  (vn ^ "." ^ (shortname fn), args)
              | _ -> assert false in
            let (prompt, args_format_s) = mk_prompt lhs in
            let scan_exp e =
              let printf_s = Format.sprintf "%s ? " prompt in
              let format_s = format_for_type ty in
              let exp_scanf = Cfun_call ("scanf", [Cconst (Cstrlit format_s); e]) in
              let body =
                if !Compiler_options.hepts_simulation
                then (* hepts: systematically test and quit when EOF *)
                  [Cif(Cbop("==",exp_scanf,Cvar("EOF")),
                       [Creturn(mk_int 0)],[])]
                else
                  [Csexpr (exp_scanf);] in
              let body =
                if !Compiler_options.hepts_simulation then
                  body
                else
                  Csexpr (Cfun_call ("printf",
                                     Cconst (Cstrlit printf_s)
                                     :: args_format_s))
                  :: body in
              Csblock { var_decls = [];
                        block_body = body; } in
            match need_buf_for_ty ty with
            | None -> ([scan_exp (Caddrof lhs)], [])
            | Some tyn ->
                let varn = fresh "buf" in
                let lhs = clhs_of_cexpr lhs in
                ([scan_exp (Cvar varn);
                  Caffect (lhs,
                           (Cfun_call (tyn ^ "_of_string",
                                     [Cvar varn])))],
                 [(varn, Cty_arr (20, Cty_char))])
        end
    | Tprod _ | Tinvalid -> failwith("read_lhs_of_ty: untranslatable type")
  in

  (* Generates printf statements and buffer declarations needed for printing
     resulting values of enum types. *)
  let rec write_lhs_of_ty lhs ty =
    match ty with
    | Tarray (ty, n) ->
        let iter_var = fresh "i" in
        let lhs = Carray (lhs, Cvar iter_var) in
        let (writes, bufs) = write_lhs_of_ty lhs ty in
        let writes_loop =
          Cfor (iter_var, mk_int 0, cexpr_of_static_exp n, writes) in
        if !Compiler_options.hepts_simulation then
          ([writes_loop], bufs)
        else
          ([cprint_string "[ ";
            writes_loop;
            cprint_string "]"], bufs)
    | (Tid tn) as ty ->
        begin match Modules.find_type tn with
        | Talias ty -> write_lhs_of_ty lhs ty
        | Tstruct field_list ->
            List.fold_left
              (fun (writes,bufs)
                 { Signature.f_name = f_name; Signature.f_type = f_ty} ->
                 let f_lhs = Cfield(lhs,f_name) in
                 let (f_writes,f_bufs) = write_lhs_of_ty f_lhs f_ty in
                 (writes@f_writes),(bufs@f_bufs))
              ([],[])
              field_list
        | _ ->
            let varn = fresh "buf" in
            let format_s = format_for_type ty in
            let format_s =
              if !Compiler_options.hepts_simulation
              then format_s ^ "\n"
              else format_s ^ " " in
            let nbuf_opt = need_buf_for_ty ty in
            let ep = match nbuf_opt with
              | None -> [lhs]
              | Some sid -> [Cfun_call ("string_of_" ^ sid,
                                        [lhs;
                                         Cvar varn])] in
            ([Csexpr (Cfun_call ("printf",
                                 Cconst (Cstrlit (format_s))
                                 :: ep))],
             match nbuf_opt with
             | None -> []
             | Some _ -> [(varn, Cty_arr (20, Cty_char))])
        end
    | Tprod _ | Tinvalid -> failwith("write_lhs_of_ty: untranslatable type")
  in

  let stepm = find_step_method cd in
  let (scanf_calls, scanf_decls) =
    let read_lhs_of_ty_for_vd vd =
      read_lhs_of_ty (Cvar (Idents.name vd.v_ident)) vd.v_type in
    split (map read_lhs_of_ty_for_vd stepm.m_inputs) in

  let (printf_calls, printf_decls) =
    let write_lhs_of_ty_for_vd vd =
      let (stm, vars) =
        write_lhs_of_ty (Cfield (Cvar "_res",
                                 local_qn (name vd.v_ident))) vd.v_type in
      if !Compiler_options.hepts_simulation then
  (stm, vars)
      else
  (cprint_string "=> " :: stm, vars)
    in
    split (map write_lhs_of_ty_for_vd stepm.m_outputs) in
  let printf_calls = List.concat printf_calls in

  let cinp = inputlist_of_ovarlist stepm.m_inputs in
  let cout = ["_res", (Cty_id (qn_append cd.cd_name "_out"))] in

  let mem_decl =
    if cd.cd_stateful
    then Some (Cvardef ("mem", Cty_id (qn_append cd.cd_name "_mem")))
    else None
  in

  let varlist =
    cinp
    @ cout
    @ concat scanf_decls
    @ concat printf_decls in

  (* The main function loops (while (1) { ... }) reading arguments for our node
     and prints the results. *)
  let step_l =
    let funcall =
      let args =
        map (fun vd -> Cvar (name vd.v_ident)) stepm.m_inputs
        @ (Caddrof (Cvar "_res")
           :: if cd.cd_stateful then [Caddrof (Cvar "mem")] else []) in
      Cfun_call ((cname_of_qn cd.cd_name) ^ "_step", args) in
    concat scanf_calls
    @ [Csexpr funcall]
    @ printf_calls
    @
      (if !Compiler_options.hepts_simulation
       then []
       else [Csexpr (Cfun_call ("puts", [Cconst (Cstrlit "")]))])
    @ [Csexpr (Cfun_call ("fflush", [Cvar "stdout"]))] in

  (* Do not forget to initialize memory via reset if needed. *)
  let rst_i =
    if cd.cd_stateful
    then [Csexpr (Cfun_call ((cname_of_qn cd.cd_name) ^ "_reset",
                             [Caddrof (Cvar "mem")]))]
    else [] in

  (mem_decl, varlist, rst_i, step_l)

(** [main_skel var_list prologue body] generates a C main() function using the
    variable list [var_list], prologue [prologue] and loop body [body]. *)
let main_skel var_list prologue body =
  Cfundef {
    C.f_name = "main";
    f_retty = Cty_int;
    f_args = [("argc", Cty_int); ("argv", Cty_ptr (Cty_ptr Cty_char))];
    f_body = {
      var_decls =
        (step_counter, Cty_int) :: (max_step, Cty_int) :: var_list;
      block_body =
        [
          (*
            step_count = 0;
            max_step = 0;
            if (argc == 2)
              max_step = atoi(argv[1]);
          *)
          Caffect (CLvar step_counter, mk_int 0);
          Caffect (CLvar max_step, mk_int 0);
          Cif (Cbop ("==", Cvar "argc", mk_int 2),
               [Caffect (CLvar max_step,
                         Cfun_call ("atoi",
                                    [Carray (Cvar "argv",
                                             mk_int 1)]))], []);
        ]
        @ prologue
          (* while (!max_step || step_c < max_step) *)
        @ [
          Cwhile (Cbop ("||",
                        Cuop ("!", Cvar max_step),
                        Cbop ("<",
                              Cvar step_counter,
                              Cvar max_step)),
                  (* step_counter = step_counter + 1; *)
                  Caffect (CLvar step_counter,
                           Cbop ("+",
                                 Cvar step_counter,
                                 mk_int 1))
                  :: body);
          Creturn (mk_int 0);
        ];
    }
  }

let mk_main name p =
  if !Compiler_options.simulation then (
      let classes = program_classes p in
      let n_names = !Compiler_options.assert_nodes in
      let find_class n =
        List.find (fun cd -> cd.cd_name.name = n) classes
      in

      let a_classes =
        List.fold_left
          (fun acc n ->
             try
               find_class n :: acc
             with Not_found -> acc)
          []
          n_names in

      let (var_l, res_l, step_l) =
        let add cd (var_l, res_l, step_l) =
          let (var, res, step) = assert_node_res cd in
          (var @ var_l, res @ res_l, step :: step_l) in
        List.fold_right add a_classes ([], [], []) in

      let n = !Compiler_options.simulation_node in
      let (defs, var_l, res_l, step_l) =
        try
          let (mem, nvar_l, res, nstep_l) = main_def_of_class_def (find_class n) in
          let defs = match mem with None -> [] | Some m -> [m] in
          (defs, nvar_l @ var_l, res @ res_l, nstep_l @ step_l)
        with Not_found -> ([],var_l,res_l,step_l) in

      [("_main.c", Csource (defs @ [main_skel var_l res_l step_l]));
       ("_main.h", Cheader ([name], []))];
  ) else
    []



(******************************)

let translate name prog =
  let modname = (Filename.basename name) in
  global_name := String.capitalize_ascii modname;
  (global_file_header modname prog) @ (mk_main name prog)

let program p =
  let filename =
    filename_of_name (cname_of_name (modul_to_string p.p_modname)) in
  let dirname = build_path (filename ^ "_c") in
  let dir = clean_dir dirname in
  let c_ast = translate filename p in
  let c_ast = if !Compiler_options.unroll_loops then List.map Cunroll.cfile c_ast else c_ast in
  C.output dir c_ast

let interface i =
  let filename =
    filename_of_name (cname_of_name (modul_to_string i.i_modname)) in
  let dirname = build_path (filename ^ "_c") in
  let dir = clean_dir dirname in
  let c_ast = interface_header (Filename.basename filename) i in
    C.output dir c_ast
