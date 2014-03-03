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

(* $Id: sigali.ml 2416 2011-01-13 17:00:15Z delaval $ *)

(* Sigali representation and output *)

type name = string

type var = name

type const = Cfalse | Cabsent | Ctrue | Cint of int

type exp =
  | Sconst of const
  | Svar of name
  | Swhen of exp * exp    (* e1 when e2 *)
  | Sdefault of exp * exp (* e1 default e2 *)
  | Sequal of exp * exp   (* e1 = e2 *)
  | Ssquare of exp        (* e^2 *)
  | Snot of exp           (* not e *)
  | Sand of exp * exp     (* e1 and e2 *)
  | Sor of exp * exp      (* e1 or e2 *)
  | Sprim of name * exp list (* f(e1,...,en) *)
  | Slist of exp list     (* [e1,...,en] *)
  | Splus of exp * exp    (* e1 + e2 *)
  | Sminus of exp * exp   (* e1 - e2 *)
  | Sprod of exp * exp    (* e1 * e2 *)

type statement = { (* name : definition *)
  stmt_name : name;
  stmt_def : exp;
}

type objective =
  | Security of exp
  | Reachability of exp
  | Attractivity of exp

type processus = {
  proc_dep : name list;
  proc_name : name;
  proc_inputs : var list;
  proc_uncont_inputs : var list;
  proc_outputs : var list;
  proc_controllables : var list;
  proc_states : var list;
  proc_init : const list;
  proc_constraints : exp list;
  proc_body : statement list;
  proc_objectives : objective list;
}

type program = processus list

let concat e1 e2 =
  Sprim("concat",[e1;e2])

let evolutions = "evolutions"
let initialisations = "initialisations"
let constraints = "constraints"

let extend var e =
  { stmt_name = var ;
    stmt_def = concat (Svar(var)) e }

let subst e1 e2 e3 =
  Sprim ("subst",[e1;e2;e3])

let l_subst e1 e2 e3 =
  Sprim ("l_subst",[e1;e2;e3])

let evolution p =
  Sprim ("evolution",[p])

let initial p =
  Sprim ("initial",[p])

let pconstraint p =
  Sprim ("constraint",[p])

let ifthenelse e1 e2 e3 =
  Sdefault(Swhen(e2,e1),e3)

let (&~) e1 e2 =
  match e1,e2 with
  | Sconst(Cfalse), _
  | _, Sconst(Cfalse) -> Sconst(Cfalse)
  | Sconst(Ctrue), e
  | e, Sconst(Ctrue) -> e
  | _ -> Sand(e1,e2)

let (|~) e1 e2 =
  match e1,e2 with
  | Sconst(Ctrue), _
  | _, Sconst(Ctrue) -> Sconst(Ctrue)
  | Sconst(Cfalse), e
  | e, Sconst(Cfalse) -> e
  | _ -> Sor(e1,e2)

let (~~) e =
  match e with
  | Sconst(Ctrue) -> Sconst(Cfalse)
  | Sconst(Cfalse) -> Sconst(Ctrue)
  | Snot(e') -> e'
  | _ -> Snot(e)

let (=>~) e1 e2 =
  match e1,e2 with
  | Sconst(Ctrue), e -> e
  | _, Sconst(Ctrue)
  | Sconst(Cfalse), _ -> Sconst(Ctrue)
  | _ -> ((~~ e1) |~ e2)

let a_const e =
  Sprim ("a_const",[e])

let a_var e e1 e2 e3 =
  Sprim ("a_var", [e;e1;e2;e3])

let a_part e e1 e2 e3 =
  Sprim ("a_part", [e;e1;e2;e3])

let a_inf e1 e2 =
  Sprim ("a_inf", [e1;e2])

let a_sup e1 e2 =
  Sprim ("a_sup", [e1;e2])

let a_iminv e1 e2 =
  Sprim ("a_iminv", [e1;e2])

module Printer =
  struct
    open Format

    let rec print_list ff print sep l =
      match l with
      | [] -> ()
      | [x] -> print ff x
      | x :: l ->
            print ff x;
          fprintf ff "%s@ " sep;
          print_list ff print sep l

    let print_name ff n =
      fprintf ff "%s" n

    let print_const ff c =
      match c with
      | Cfalse ->  fprintf ff "-1"
      | Ctrue ->   fprintf ff "1"
      | Cabsent -> fprintf ff "0"
      | Cint(v) -> fprintf ff "%d" v

    let rec print_exp ff e =
      match e with
      | Sconst(c) -> print_const ff c
      | Svar(v) -> print_name ff v
      | Swhen(e1,e2) ->
          fprintf ff "(%a@ when %a)"
            print_exp e1
            print_exp e2
      | Sdefault(e1,e2) ->
          fprintf ff "(%a@ default %a)"
            print_exp e1
            print_exp e2
      | Sequal(e1,e2) ->
          fprintf ff "(%a@ = %a)"
            print_exp e1
            print_exp e2
      | Ssquare(e) ->
          fprintf ff "(%a^2)"
            print_exp e
      | Snot(e) ->
          fprintf ff "(not %a)"
            print_exp e
      | Sand(e1,e2) ->
          fprintf ff "(%a@ and %a)"
            print_exp e1
            print_exp e2
      | Sor(e1,e2) ->
          fprintf ff "(%a@ or %a)"
            print_exp e1
            print_exp e2
      | Sprim(f,e_l) ->
          fprintf ff "%s(@[" f;
          print_list ff print_exp "," e_l;
          fprintf ff "@])"
      | Slist(e_l) ->
          fprintf ff "[@[";
          print_list ff print_exp "," e_l;
          fprintf ff "]@]"
      | Splus(e1,e2) ->
          fprintf ff "(%a@ + %a)"
            print_exp e1
            print_exp e2
      | Sminus(e1,e2) ->
          fprintf ff "(%a@ - %a)"
            print_exp e1
            print_exp e2
      | Sprod(e1,e2) ->
          fprintf ff "(%a@ * %a)"
            print_exp e1
            print_exp e2

    let print_statement ff { stmt_name = name; stmt_def = e } =
      fprintf ff "@[<hov 2>%a : %a;@]"
        print_name name
        print_exp e

    let print_statements ff stmt_l =
      fprintf ff "@[<v>";
      print_list ff print_statement "" stmt_l;
      fprintf ff "@]@ "

    let print_objective name ff obj =
      match obj with
      | Security(e) ->
          fprintf ff "%s : S_Security(%s,B_True(%s,%a));"
            name name name
            print_exp e
      | Reachability(e) ->
          fprintf ff "%s : S_Reachable(%s,B_True(%s,%a));"
            name name name
            print_exp e
      | Attractivity(e) ->
          fprintf ff "%s : S_Attractivity(%s,B_True(%s,%a));"
            name name name
            print_exp e

    let print_verification name ff obj =
      match obj with
      | Security(e) ->
          fprintf ff "verif_result : verif_result andb notb Reachable(%s,B_False(%s,%a));"
            name name
            print_exp e
      | Reachability(e) ->
          fprintf ff "verif_result : verif_result andb Reachable(%s,B_True(%s,%a));"
            name name
            print_exp e
      | Attractivity(_) -> failwith("Attractivity verification not allowed")

    let sigali_head = "set_reorder(2);\
                       read(\"Property.lib\");\
                       read(\"Synthesis.lib\");\
                       read(\"Verif_Determ.lib\");\
                       read(\"Simul.lib\");\
                       read(\"Synthesis_Partial_order.lib\");\
                       read(\"Orbite.lib\");"

    let sigali_foot = ""

    let print_processus dir ({ proc_dep = dep_list;
                               proc_name = name;
                               proc_inputs = inputs;
                               proc_uncont_inputs = uncont_inputs;
                               proc_outputs = outputs;
                               proc_controllables = controllables;
                               proc_states = states;
                               proc_constraints = constraints;
                               proc_body = body;
                               proc_objectives = objectives;
                             }) =
      let sigc = open_out (dir ^ "/" ^ name ^ ".z3z") in
      let ff = formatter_of_out_channel sigc in

      Compiler_utils.print_header_info ff "%" "%";
      fprintf ff "%s" sigali_head;
      (* let n = List.length states in *)

      (* declare dummy variables d1...dn *)
      (* fprintf ff "@[declare(@[<hov>d1"; *)
      (* for i = 2 to n do *)
      (*   fprintf ff ",@ d%d" i; *)
      (* done; *)
      (* fprintf ff "@]);@]@\n@\n"; *)

      fprintf ff "@[<v>";

      (* dependencies *)
      fprintf ff "%% -- dependencies --- %%@\n@\n";

      List.iter
        (fun dep_name ->
           fprintf ff "read(\"%s.z3z\");@\n" dep_name)
        dep_list;

      (* head comment *)
      fprintf ff "%% ---------- process %s ---------- %%@\n@\n" name;

      (* variables declaration *)
      fprintf ff "declare(@[<hov>";
      print_list ff print_name "," (inputs@states);
      fprintf ff "@]);@,";

      (* inputs decl. *)
      fprintf ff "conditions : [@[";
      print_list ff print_name "," inputs;
      fprintf ff "@]];@,";

      (* states decl. *)
      fprintf ff "states : [@[";
      if states = [] then
        (* dummy state var to avoid sigali segfault *)
        fprintf ff "d1"
      else
        print_list ff print_name "," states;
      fprintf ff "@]];@,";

      (* controllables : *)
      fprintf ff "controllables : [@[";
      print_list ff print_name "," controllables;
      fprintf ff "@]];@,";

      (* init evolutions, initialisations *)
      if states = [] then
        fprintf ff "evolutions : [d1];@,"
      else
        fprintf ff "evolutions : [];@,";
      fprintf ff "initialisations : [];@,";

      (* body statements *)
      print_statements ff body;

      (* constraints *)
      fprintf ff "constraints : [@[";
      print_list ff print_exp "," constraints;
      fprintf ff "@]];@,";

      (* outputs : comment *)
      fprintf ff "@,%% --- outputs : [@[";
      print_list ff print_name "," outputs;
      fprintf ff "@]] --- %%@,";

      (* process declaration *)
      fprintf ff
        ("%s : processus(" ^^
           "@[conditions," ^^
           "@ states," ^^
           "@ evolutions," ^^
           "@ initialisations," ^^
           "@ [gen(constraints)]," ^^
           "@ controllables@]);@,")
        name;

      begin
        match controllables with
          [] ->
            begin
              (* No controllable variables: verification *)

              (* Initialisation of verification result *)
              fprintf ff "verif_result : True;@,";

              (* Verification of properties (update verif_result) *)
              fprintf ff "@[<v>";
              print_list ff (print_verification name) "" objectives;
              fprintf ff "@]@,";

              (* Print result *)
              fprintf ff "if verif_result then@,";
              fprintf ff "    print(\"%s: property true.\")@," name;
              fprintf ff "else@,";
              fprintf ff "    print(\"%s: property false.\");@," name;
            end

        | _::_ ->
            begin
              (* At least one controllable variable: synthesis *)

              (* Store the initial state for further check *)
              fprintf ff "%s_init : initial(%s);@," name name;

              (* Controller synthesis *)
              fprintf ff "@[<v>";
              print_list ff (print_objective name) "" objectives;
              fprintf ff "@]@,";

              (* Check that synthesis succeeded : initial state not modified *)
              fprintf ff "dcs_result : equal(%s_init,initial(%s));@," name name;

              (* Print result *)
              fprintf ff "if dcs_result then@,";
              fprintf ff "    print(\"%s: synthesis succeeded.\")@," name;
              fprintf ff "else@,";
              fprintf ff "    print(\"%s: synthesis failed.\");@," name;

              fprintf ff "@\nif dcs_result then@,";
              (* Controller output *)
              (*       fprintf ff "    simul(%s,\"%s.res\",\"%s.sim\")@\n" name name name; *)
              fprintf ff "    print(\"Triangulation and controller generation...\")@\n";
              fprintf ff "else@,";
              fprintf ff "    quit(1);@,";

              (* Triangulation *)
              (* phantoms : *)
              let phantom_vars = List.map (fun n -> "p_" ^ n) controllables in
              (* phantom variables declaration *)
              fprintf ff "declare(@[<hov>";
              print_list ff print_name "," phantom_vars;
              fprintf ff "@]);@,";
              fprintf ff "phantom_vars : [@[";
              print_list ff print_name "," phantom_vars;
              fprintf ff "@]];@,";
              fprintf ff "%s_triang : Triang(constraint(%s),controllables,phantom_vars);@,"
                name name;


              let states =
                match !Compiler_options.nosink with
                  true -> states
                | false ->
                    (* Suppress sink state as controller input *)
                    List.rev (List.tl (List.rev states)) in
              (* controller vars *)
              fprintf ff "controller_inputs : [@[";
              print_list ff print_name "," (uncont_inputs
                                            @states
                                            @(List.map
                                                (fun n -> "p_" ^ n)
                                                controllables));
              fprintf ff "@]];@,";

              (* Controller generation *)
              fprintf ff "heptagon_controller(\"%s_controller.ept\",\"%s\",\
                          controller_inputs,controllables,%s_triang);@," name name name;
            end
      end;

      (* Footer and close file *)
      fprintf ff "@]@.";
      fprintf ff "%s" sigali_foot;
      fprintf ff "@?";

      close_out sigc


    let print dir p_l =
      List.iter (print_processus dir) p_l
  end
