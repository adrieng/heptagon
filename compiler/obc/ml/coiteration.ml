(**************************************************************************)
(*                                                                        *)
(*  Lucid Synchrone                                                       *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* $Id: coiteration.ml,v 1.27 2008-06-10 06:54:36 delaval Exp $ *)


(** Translating [declarative] code into sequential [caml] code. *)

open Misc
open Names
open Declarative
open Rw
open Dmisc
open Caml
open Cenvironment

let prefix_for_names = "_"
let prefix_for_inits = "_init"
let prefix_for_memos = "_pre"
let prefix_for_statics = "_static"
let prefix_for_clocks = "_cl"
let prefix_for_lasts = "__last"

let prefix_state_type = "_state_"
let prefix_state_constr = "`St_"
let prefix_state_label = "_mem_"
let prefix_state_constr_nil = "`Snil_"
let prefix_for_self_state = "_self_"
let prefix_for_temp = "_temp_"

(** the type of unknown states *)
(* type 'a state = Snil | St of 'a *)
let state_nil = Cconstruct(qualid prefix_state_constr_nil, [])
let state_nil_pat = Cconstructpat(qualid prefix_state_constr_nil, [])
let state_pat pat_list = Cconstructpat(qualid prefix_state_constr, pat_list)
let state e_list = Cconstruct(qualid prefix_state_constr, e_list)
let state_record name_e_list =
  Crecord(List.map (fun (name, e) -> (qualid name), e) name_e_list)

let intro_state_type () =
  let tname = prefix_state_type in
  let result_type =
    Dconstr(qualid prefix_state_type, [Dtypvar(0)]) in
  let variants =
    [(qualid prefix_state_constr_nil, { arg = []; res = result_type });
     (qualid prefix_state_constr, {arg = [Dtypvar(0)]; res = result_type})]
  in
  let type_def =
    { d_type_desc = Dvariant_type(variants);
      d_type_arity = [0] } in
  add_type (tname, type_def)

(** introduce a new type for enumerated states *)
(* type ('a1,...,'an) state_k = St1 of 'a1 | ... Stm of 'an *)
let intro_enum_type n =
  let l = Misc.from n in
  (* name of the result type *)
  let tname = prefix_state_type ^ (string_of_int(symbol#name)) in
  let result_type =
    Dconstr(qualid tname, List.map (fun name -> Dtypvar(name)) l) in
  let variants =
    List.map
      (fun name ->
  (qualid (tname ^ prefix_state_constr ^ (string_of_int name)),
   { arg = [Dtypvar(name)]; res = result_type })) l in
  let type_def =
    { d_type_desc = Dvariant_type(variants);
      d_type_arity = l } in
  add_type (tname, type_def);
  tname ^ prefix_state_constr

(** introduce a new type for record states *)
(* type ('a1,...,'an) state_k = {mutable name1:a1;...;mutable namen:an} *)
let intro_record_type name_value_list =
  let l = Misc.from (List.length name_value_list) in
  let tname = prefix_state_type ^ (string_of_int(symbol#name)) in
  let result_type =
    Dconstr(qualid tname, List.map (fun name -> Dtypvar(name)) l) in
  let labels =
    List.map2
      (fun (name,_) ai ->
  (qualid name,
   true,
   { res = Dtypvar(ai); arg = result_type })) name_value_list l in
  let type_def =
    { d_type_desc = Drecord_type(labels);
      d_type_arity = l } in
  add_type (tname, type_def)

(** the intermediate code generated during the compilation process *)
type tcode =
    Tlet of pattern * cexp
  | Tset of string * cexp
  | Tlabelset of string * string * cexp
  | Tletrec of (pattern * cexp) list
  | Texp of cexp

(* and its translation into caml code *)
let rec clet tcode ce =
  let code2c tcode ce =
    match tcode with
      Tlet(p, c) -> Clet(false, [p,c], ce)
    | Tset(s, e) -> cseq (Cset(s,e)) ce
    | Tlabelset(s, n, e) -> cseq (Clabelset(s, n, e)) ce
    | Tletrec(l) -> Clet(true, l, ce)
    | Texp(c) when ce = cvoid -> c
    | Texp(c) -> cseq c ce in
  match tcode with
    [] -> ce
  | tc :: tcode -> code2c tc (clet tcode ce)

let cseq tcode = clet tcode cvoid
let ifthen c ce =
  match c with
    Cconstant(Cbool(true)) -> ce
  | _ -> Cifthen(c, ce)

let merge code ce l =
  (* we make special treatments for conditionals *)
  match l with
    [] -> code
  | [Cconstantpat(Cbool(b1)), c1;
     Cconstantpat(Cbool(b2)), c2] ->
       if b1 then
   Texp(Cifthenelse(ce, c1, c2)) :: code
       else
   Texp(Cifthenelse(ce, c2, c1)) :: code
  (* general case *)
  | _ -> Texp(Cmatch(ce, l)) :: code


(** extract the set of static computations from an expression *)
let rec static acc e =
  let acc, desc = match e.d_desc with
  | Dconstant _ | Dvar _ | Dfun _ -> acc, e.d_desc
  | Dtuple l ->
      let acc, l = static_list acc l in
      acc, Dtuple(l)
  | Dprim(g, e_list) ->
      (* pointwise application *)
      let acc, e_list = static_list acc e_list in
      acc, Dprim(g, e_list)
  | Dconstruct(g, e_list) ->
      let acc, e_list = static_list acc e_list in
      acc, Dconstruct(g, e_list)
  | Drecord(gl_expr_list) ->
      let static_record (gl, expr) (acc, gl_expr_list) =
  let acc, e = static acc expr in
  acc, (gl, e) :: gl_expr_list in
      let acc, l =
  List.fold_right static_record gl_expr_list (acc, []) in
      acc, Drecord(l)
  | Drecord_access(expr, gl) ->
      let acc, e = static acc expr in
      acc, Drecord_access(e, gl)
  | Difthenelse(e0, e1, e2) ->
      let acc, e0 = static acc e0 in
      let acc, e1 = static acc e1 in
      let acc, e2 = static acc e2 in
      acc, Difthenelse(e0, e1, e2)
  | Dlet(block, e_let) ->
      let acc, block = static_block acc block in
      let acc, e = static acc e_let in
      acc, Dlet(block, e_let)
  | Dapply(is_state, f, l) ->
      let acc, f = static acc f in
      let acc, l = static_list acc l in
      acc, Dapply(is_state, f, l)
  | Deseq(e1, e2) ->
      let acc, e1 = static acc e1 in
      let acc, e2 = static acc e2 in
      acc, Deseq(e1, e2)
  | Dwhen(e1) ->
      let acc, e1 = static acc e1 in
      acc, Dwhen(e1)
  | Dclock(ck) ->
      acc, Dclock(ck)
  | Dlast _ | Dinit _ | Dpre _ | Dtest _ ->
      (* this case should not arrive *)
      fatal_error "static" in
  acc, { e with d_desc = desc }

and static_list acc l =
  match l with
    [] -> acc, []
  | e :: l ->
      let acc, e = static acc e in
      let acc, l = static_list acc l in
      acc, e :: l

and static_block acc b =
  let acc, eq = static_eq acc b.b_equations in
  acc, { b with b_equations = eq }

(* extract the set of static computations from an equation *)
and static_eqs acc eq_list =
  match eq_list with
    [] -> acc, []
  | eq :: eq_list ->
      let acc, eq = static_eq acc eq in
      let acc, eq_list = static_eqs acc eq_list in
      acc, dcons eq eq_list

and static_eq acc eq =
  match eq with
    Dget _ -> acc, eq
  | Dequation(pat, e) ->
      let acc, e = static acc e in
      acc, Dequation(pat, e)
  | Dwheneq(eq, ck) ->
      let acc, eq = static_eq acc eq in
      acc, Dwheneq(eq, ck)
  | Dmerge(is_static, e, p_block_list) ->
      let acc, e = static acc e in
      let acc, p_block_list = static_pat_block_list acc p_block_list in
      acc, Dmerge(is_static, e, p_block_list)
  | Dnext(n, e) ->
      let acc, e = static acc e in
      acc, Dnext(n, e)
  | Dseq(eq_list) ->
      let acc, eq_list = static_eqs acc eq_list in
      acc, Dseq(eq_list)
  | Dpar(eq_list) ->
      let acc, eq_list = static_eqs acc eq_list in
      acc, Dpar(eq_list)
  | Dblock(block) ->
      let acc, block = static_block acc block in
      acc, Dblock(block)
  | Dstatic(pat, e) ->
      (pat, e) :: acc, no_equation
  | Demit _ | Dlasteq _ | Dautomaton _ | Dreset _ | Dpresent _ ->
      (* these cases should not arrive since control structures have *)
      (* been translated into the basic kernel *)
      fatal_error "static_eq"

and static_pat_block_list acc p_block_list =
  (* treat one handler *)
  let static_pat_block acc (pat, block) =
    let acc, block = static_block acc block in
    acc, (pat, block) in
  match p_block_list with
    [] -> acc, []
  | pat_block :: pat_block_list ->
      let acc, pat_block = static_pat_block acc pat_block in
      let acc, pat_block_list = static_pat_block_list acc pat_block_list in
      acc, pat_block :: pat_block_list

(** Auxiliary definitions **)
let string_of_ident ident =
  let prefix =
    match ident.id_kind with
      Kinit -> prefix_for_inits
    | Kstatic -> prefix_for_statics
    | Kmemo -> prefix_for_memos
    | Kclock -> prefix_for_clocks
    | Klast -> prefix_for_lasts
    | _ -> prefix_for_names in
  let suffix =
    match ident.id_original with
      None -> ""
    | Some(n) when (is_an_infix_or_prefix_operator n) -> "__infix"
    | Some(n) -> "__" ^ n in
  prefix ^ (string_of_int ident.id_name) ^ suffix

let string_of_name env i =
  (* find the original name when it exists *)
  let ident = find env i in
  string_of_ident ident

let name i = prefix_for_names ^ (string_of_int i)
let memo i = prefix_for_memos ^ (string_of_int i)
let initial i = prefix_for_inits ^ (string_of_int i)
let clock i = prefix_for_clocks ^ (string_of_int i)
let stat i = prefix_for_statics ^ (string_of_int i)

(* the name of the current state *)
let selfstate env = prefix_for_self_state ^ (string_of_int (statename env))

(* access to a write variable *)
let access_write wt s = Cderef (Cvar s)

(* makes an access to a name *)
let access env i =
  let ident, st, wt = findall env i in
  let s = string_of_ident ident in
  match ident.id_kind with
    Kinit | Kmemo | Kstatic ->
      Crecord_access(Cvar(prefix_for_self_state ^ (string_of_int st)),
         qualid s)
  | _ ->
      if is_a_write ident
      then access_write wt s
      else Cvar(s)

let set name c = Tset(name, c)
let next self name c = Tlabelset(self, name, c)

(** Compilation of functions *)
(*  x1...xn.<init, code, res> is translated into

   (1) combinatorial function

       \x1...xn.code;res

   (2) \x1...xn.self.
       let self = match !self with
                    Nil -> let v = { ... init ... } in
                           self := St(v);v
                  | St(self) -> self in
       code;
       res

   r = f [...] x1...xn is translated into:

   (1) combinatorial function

   f = f [...] x1...xn

   (2) state function

   st = ref Nil       initialisation part

   r = f x1...xn st   step part

Rmk: we can also write: "if reset then self := { ... }"
*)

let co_apply env is_state (init_write, init_mem) f subst e_list =
  if is_state then
    (* state function *)
    let st = prefix_for_names ^ (string_of_int symbol#name) in
    let prefix = selfstate env in
    (init_write, (st, Cref(state_nil)) :: init_mem),
    Capply(f,
     (subst @ e_list @ [Crecord_access(Cvar(prefix), qualid st)]))
  else
    (init_write, init_mem), Capply(f, subst @ e_list)

(* prepare the initialization of memory variables *)
let cmatchstate self states =
  let v = prefix_for_names ^ (string_of_int (symbol#name)) in
  let st = prefix_state_constr ^ (string_of_int (symbol#name)) in
  Cmatch(Cderef(Cvar(self)),
   [Cconstructpat(qualid st,[Cvarpat(self)]), Cvar(self);
    Cwildpat, Clet(false, [Cvarpat(v), states],
            Cseq[Cset(self,
          Cconstruct(qualid st, [Cvar(v)]));
           Cvar(v)])])

(* prepare the initialization of write variables *)
let define_init_writes env init_write code =
  List.fold_right
    (fun (name, e) code -> Clet(false, [Cvarpat(name), Cref e], code))
    init_write code

let co_fun env
    is_state params p_list static (init_write, init_mem) code result =
  if init_mem <> [] then intro_record_type init_mem;

  let code = clet code result in
  let code =
    if init_write <> []
    then define_init_writes env init_write code
    else code in
  let self = selfstate env in
  if is_state
  then
    if init_mem = [] then Cfun(params @ p_list @ [Cvarpat(self)], code)
    else Cfun(params @ p_list @ [Cvarpat(self)],
        Clet(false, [Cvarpat(self),
         cmatchstate self
           (clet static (state_record init_mem))],
       code))
  else Cfun(params @ p_list, code)

(** Compilation of pattern matching *)
(*
  match e with
    P1 -> e1
  | ...
  | Pn -> en

(1) e is a static computation

- initialisation code
  let memory = match e with
               P1 -> St1 { ... }
             | ...
             | Pn -> Stn { ... }

- step code
  match memory with
  St1{...} -> step1
| ...
| Stn{...} -> stepn

(2) e may evolve at every instant

- init code
  ...i1...
  ...in...

- match e with
    P1 -> step1
  | ...
  | Pn -> stepn

for the moment, we treat case (1) as case (2) *)

(*
let co_static_merge e (pat, init_code_fvars_list) =
  (* introduces the type definitions for the representation of states *)
  let n = List.length init_code_fvars_list in
  let prefix_constructor = intro_enum_type n in

  (* builds a constructor value *)
  let constructor prefix number f_vars =
    Cconstruct(qualid (prefix ^ (string_of_int number)),
         List.map (fun name -> Cvar(name)) fvars) in
  let constructor_pat prefix number f_vars =
    Cconstructpat(qualid (prefix ^ (string_of_int number)),
      List.map (fun name -> Cvarpat(name)) fvars) in

  (* computes the initialisation part *)
  let rec states number init_code_fvars_list =
    match init_code_fvars_list with
      [] -> []
    | (pat, init, _, fvars) :: init_code_fvars_list ->
  let pat_code = (pat, clet init (constructor prefix number fvars)) in
  let pat_code_list = states (number + 1) init_code_fvars_list in
  pat_code :: code_list in

  (* computes the transition part *)
  let rec steps number init_code_fvars_list =
    match init_code_fvars_list with
      [] -> []
    | (_, _, code, fvars) :: init_code_fvars_list ->
  let pat_code = (constructor_pat prefix number fvars, code) in
  let pat_code_list = steps (number + 1) init_code_fvars_list in
  pat_code :: pat_code_list in

  (* make the final code *)
  let memory = symbol#name in
  let init_code = Cmatch(e, states 0 init_code_fvars_list) in
  let step_code = Cmatch(Cvar memory, steps 0 init_code_fvars_list) in
  Tlet(memory, init_code), step_code

*)

(** Compilation of clocks *)
let rec translate_clock env init ck =
  match ck with
    Dfalse ->  init, cfalse
  | Dtrue -> init, ctrue
  | Dclockvar(n) -> init, access env n
  | Don(is_on, ck, car) ->
      let init, ck = translate_clock env init ck in
      let init, car = translate_carrier env init car in
      init, if is_on then cand car ck
      else cand (cnot car) ck

and translate_carrier env init car =
  match car with
    Dcfalse -> init, cfalse
  | Dctrue -> init, ctrue
  | Dcvar(n) -> init, access env n
  | Dcglobal(g, res, ck) ->
      (* a global clock allocates memory *)
      (* and is compiled as a function call *)
      let res = match res with None -> cfalse | Some(n) -> access env n in
      let init, c = translate_clock env init ck in
      let init, new_ce =
  co_apply env true init (Cglobal g) [c] [res] in
      init, new_ce

(** Compiling immediate. *)
let translate_immediate i =
  match i with
  | Dbool(b) -> Cbool(b)
  | Dint(i) -> Cint(i)
  | Dfloat(f) -> Cfloat(f)
  | Dchar(c) -> Cchar(c)
  | Dstring(s) -> Cstring(s)
  | Dvoid -> Cvoid

(** Compiling variables. *)
let translate_var env v =
  match v with
    Dglobal(g) -> Cglobal(g)
  | Dlocal(n) -> access env n

(** Compiling a pattern. *)
let rec translate_pat env pat =
  match pat with
  | Dconstantpat(i) -> Cconstantpat(translate_immediate(i))
  | Dvarpat(s) -> Cvarpat(string_of_name env s)
  | Dtuplepat(l) -> Ctuplepat(List.map (translate_pat env) l)
  | Dconstructpat(gl, pat_list) ->
      Cconstructpat(gl, List.map (translate_pat env) pat_list)
  | Dorpat(pat1, pat2) -> Corpat(translate_pat env pat1,
         translate_pat env pat2)
  | Drecordpat(gl_pat_list) ->
      Crecordpat
  (List.map (fun (gl, pat) -> (gl, translate_pat env pat))
     gl_pat_list)
  | Daliaspat(pat, i) -> Caliaspat(translate_pat env pat,
           string_of_name env i)
  | Dwildpat -> Cwildpat

(*
(* add accesses to write variables defined in patterns *)
let rec add_write_access env code pat =
  match pat with
    Dconstantpat(i) -> code
  | Dvarpat(s) when is_a_write (find env s) ->
      Tset(string_of_name env s, access env s) :: code
  | Dvarpat _ -> code
  | Dtuplepat(l) | Dconstructpat(_, l) ->
      List.fold_left (add_write_access env) code l
  | Dorpat(pat1, pat2) ->
      add_write_access env (add_write_access env code pat1) pat2
  | Drecordpat(gl_pat_list) ->
      List.fold_left (fun code (_, pat) -> add_write_access env code pat)
  code gl_pat_list
  | Daliaspat(pat, i) ->
      add_write_access env (add_write_access env code pat) (Dvarpat(i))
  | Dwildpat -> code
*)

(** Compiling an expression *)
(* takes an environment giving information about variables *)
(* and an expression and returns the new code              *)
let rec translate env init e =
  match e.d_desc with
  | Dconstant(i) ->
      let i = translate_immediate i in
      init, Cconstant(i)
  | Dvar(v, subst) ->
      let v = translate_var env v in
      let init, s = translate_subst env init subst in
      let v = match s with [] -> v | l -> Capply(v, l) in
      init, v
  | Dtuple l ->
      let init, lc = translate_list env init l in
      init, Ctuple(lc)
  | Dfun(is_state, params, p_list, body, result) ->
      (* state function *)
      let env = push_block body env in
      (* compiles types and clock abstractions *)
      let params = translate_forall env params in
      (* compiles parameters *)
      let p_list = List.map (translate_pat env) p_list in
      (* remove static computation from the body *)
      (* and put it in the allocation place for stateful functions *)
      let (static_code, init_code, body, result) =
  if is_state
  then
    let static_code, body = static_block [] body in
    let static_code, result = static static_code result in
    let static_code = List.rev static_code in
    (* translate the static code *)
    let static_code, init_code =
      translate_static_code env static_code in
    (static_code, init_code, body, result)
  else
    ([], ([], []), body, result) in
      (* then translate the body *)
      let init_code, body = translate_block env init_code body in
      let init_code, result = translate env init_code result in
      init,
      co_fun env is_state params p_list static_code init_code body result
  | Dprim(g, e_list) ->
      (* pointwise application *)
      let init, ce_list = translate_list env init e_list in
      init, Capply(Cglobal(g), ce_list)
  | Dconstruct(g, e_list) ->
      let init, ce_list = translate_list env init e_list in
      init, Cconstruct(g, ce_list)
  | Drecord(gl_expr_list) ->
      let translate_record (gl, expr) (init, gl_expr_list) =
  let init, ce = translate env init expr in
  init, (gl, ce) :: gl_expr_list in
      let init, l =
  List.fold_right translate_record gl_expr_list (init, []) in
      init, Crecord(l)
  | Drecord_access(expr, gl) ->
      let init, ce = translate env init expr in
      init, Crecord_access(ce, gl)
  | Difthenelse(e0, e1, e2) ->
      let init, c0 = translate env init e0 in
      let init, c1 = translate env init e1 in
      let init, c2 = translate env init e2 in
      init, Cifthenelse(c0, c1, c2)
  | Dlet(block, e_let) ->
      let env = push block env in
      let init, code = translate_block env init block in
      let init, ce = translate env init e_let in
      init, clet code ce
  | Dapply(is_state, { d_desc = Dvar(f, subst) }, l) ->
      let f = translate_var env f in
      let init, l = translate_list env init l in
      let init, subst = translate_subst env init subst in
      co_apply env is_state init f subst l
  | Dapply(is_state, f, l) ->
      let init, f = translate env init f in
      let init, l = translate_list env init l in
      co_apply env is_state init f [] l
  | Deseq(e1, e2) ->
      let init, e1 = translate env init e1 in
      let init, e2 = translate env init e2 in
      init, Cseq [e1; e2]
  | Dwhen(e1) ->
      translate env init e1
  | Dclock(ck) ->
      translate_clock env init ck
  | Dlast _ | Dinit _ | Dpre _ | Dtest _ ->
      (* this case should not arrive *)
      fatal_error "translate"

and translate_list env init l =
  match l with
    [] -> init, []
  | ce :: l ->
      let init, ce = translate env init ce in
      let init, l = translate_list env init l in
      init, ce :: l

and translate_block env init b =
  (* allocate the memory in the initialisation part *)
  let init = allocate_memory env init in
  (* compiles the body *)
  let init, code = translate_equation env init [] b.b_equations in
  (* sets code in the correct order *)
  let code = List.rev code in
  (* returns the components of the block *)
  init, code

(* the input equations must be already scheduled *)
and translate_equations env init code eq_list =
  match eq_list with
    [] -> init, code
  | eq :: eq_list ->
      let init, code = translate_equation env init code eq in
      translate_equations env init code eq_list

and translate_equation_into_exp env init eq =
  let init, code = translate_equation env init [] eq in
  (* sets code in the correct order *)
  let code = List.rev code in
  init, cseq code

and translate_block_into_exp env init block =
  let init, code = translate_block env init block in
  init, cseq code

and translate_equation env init code eq =
  match eq with
    Dget(pat, v) ->
      let cpat = translate_pat env pat in
      let n = translate_var env v in
      init, Tlet(cpat, n) :: code
  | Dequation(Dvarpat(n), e) when is_a_write (find env n) ->
      let name = string_of_name env n in
      let init, ce = translate env init e in
      init, (set name ce) :: code
  | Dequation(pat, e) | Dstatic(pat, e) ->
      let is_rec = is_recursive pat e in
      let pat = translate_pat env pat in
      let init, ce = translate env init e in
      init, if is_rec then Tletrec([pat, ce]) :: code
            else Tlet(pat, ce) :: code
  | Dwheneq(eq, ck) ->
      let init, ce = translate_equation_into_exp env init eq in
      let init, ck_ce = translate_clock env init ck in
      init, Texp(ifthen ck_ce ce) :: code
  | Dmerge(is_static, e, p_block_list) ->
      let init, ce = translate env init e in
      let init, l = translate_pat_block_list env init p_block_list in
      init, merge code ce l
  | Dnext(n, e) ->
      (* n is either a memo or an initialisation variable *)
      let init, ce = translate env init e in
      init, (next (selfstate env) (string_of_name env n) ce) :: code
  | Dseq(eq_list) | Dpar(eq_list) ->
      translate_equations env init code eq_list
  | Dblock(block) ->
      translate_block env init block
  | Demit _ | Dlasteq _ | Dautomaton _ | Dreset _ | Dpresent _ ->
      (* these cases should not arrive since control structures have *)
      (* been translated into the basic kernel *)
      fatal_error "translate_equation"

(* compilation of pattern matching *)
and translate_pat_block_list env init p_block_list =
  (* compile one handler *)
  let translate_pat_block init (pat, block) =
    let env = push block env in
    let cpat = translate_pat env pat in
    let init, ce = translate_block_into_exp env init block in
    init, (cpat, ce) in
  match p_block_list with
    [] -> init, []
  | pat_block :: pat_block_list ->
      let init, pat_ce = translate_pat_block init pat_block in
      let init, pat_ce_list =
  translate_pat_block_list env init pat_block_list in
      init, pat_ce :: pat_ce_list

(* translate a pure (stateless) expression *)
and translate_pure env e =
  let init, ce = translate env ([], []) e in
  assert (init = ([], []));
  ce

(* computes extra parameters for clock abstraction *)
and translate_forall env params =
  let p_clocks =
    List.map (fun n -> Cvarpat(string_of_name env n)) params.s_clock in
  let p_carriers =
    List.map (fun n -> Cvarpat(string_of_name env n)) params.s_carrier in
  p_clocks @ p_carriers

(* generates an application for clock instanciation *)
and translate_subst env init subst =
  let rec translate_clock_list init cl_list =
    match cl_list with
      [] -> init, []
    | cl :: cl_list ->
  let init, cl = translate_clock env init cl in
  let init, cl_list = translate_clock_list init cl_list in
  init, cl :: cl_list in
  let rec translate_carrier_list init car_list =
    match car_list with
      [] -> init, []
    | car :: car_list ->
  let init, car = translate_carrier env init car in
  let init, car_list = translate_carrier_list init car_list in
  init, car :: car_list in
  let init, cl_list = translate_clock_list init subst.s_clock in
  let init, car_list = translate_carrier_list init subst.s_carrier in
  init, cl_list @ car_list

(* Initialisation code *)
and allocate_memory env init =
  let allocate _ ident (acc_write, acc_mem) =
    match ident.id_kind with
      Kmemo ->
  (* we allocate only one cell *)
  let default = default_value env ident in
  acc_write, (memo ident.id_name, default) :: acc_mem
    | Kinit ->
  (* init variables are considered to be state variables *)
  acc_write, (initial ident.id_name, Cconstant(Cbool(true))) :: acc_mem
    | _ when is_a_write ident ->
  (* local write variables are allocated too *)
  (* but they will be stored in a stack allocated structure *)
  let name = string_of_name env ident.id_name in
  let default = default_value env ident in
  (name, default) :: acc_write, acc_mem
    | _ -> acc_write, acc_mem in
  Hashtbl.fold allocate (cblock env).b_env init

(* add static code into the initialisation part *)
and translate_static_code env static_code =
  (* add one equation *)
  (* we compute the list of introduced names and compile the equation *)
  let translate_eq acc (pat, e) =
    let acc = fv_pat acc pat in
    let pat = translate_pat env pat in
    let ce = translate_pure env e in
    acc, Tlet(pat, ce) in
  let rec translate_static_code acc static_code =
    match static_code with
      [] -> acc, []
    | pat_e :: static_code ->
        let acc, cpat_ce = translate_eq acc pat_e in
        let acc, static_code = translate_static_code acc static_code in
        acc, cpat_ce :: static_code in
  (* introduced names must be added to the memory *)
  let intro acc_mem n =
    let v = string_of_name env n in
    (* modify the kind of [n] *)
    set_static (find env n);
    (string_of_name env n, Cvar(v)) :: acc_mem in

  (* first compile the static code *)
  let acc, static_code = translate_static_code [] static_code in
  (* introduced names must be added to the memory initialisation *)
  let acc_mem = List.fold_left intro [] acc in
  static_code, ([], acc_mem)

(* default value *)
and default_value env ident =
  (* find a value from a type *)
  let rec value ty =
    match ty with
      Dproduct(ty_l) -> Ctuple(List.map value ty_l)
    | Dbase(b) ->
  let v = match b with
    Dtyp_bool -> Cbool(false)
  | Dtyp_int -> Cint(0)
  | Dtyp_float -> Cfloat(0.0)
  | Dtyp_unit -> Cvoid
  | Dtyp_char -> Cchar(' ')
  | Dtyp_string -> Cstring("") in
  Cconstant(v)
    | Dsignal(ty) -> Ctuple[value ty; cfalse]
    | Dtypvar _ | Darrow _ -> cdummy
    | Dconstr(qualid, _) ->
  try
    let desc = find_type qualid in
    match desc.d_type_desc with
        Dabstract_type -> cdummy
      | Dabbrev(ty) ->
    value ty
      | Dvariant_type l ->
        let case = List.hd l in
        begin match case with
    (qual, { arg = ty_l }) ->
      Cconstruct(qual, List.map value ty_l)
        end
    | Drecord_type l ->
        let field_of_type (qual, _, ty_ty) = (qual, value ty_ty.res) in
        Crecord (List.map field_of_type l)
  with
    Not_found -> cdummy  in
  let value (Dtypforall(_, ty)) = value ty in
  match ident.id_value with
    None -> value ident.id_typ
  | Some(e) -> translate_pure env e

(** Compilation of a table of declarative code *)
let translate table =
  let translate (s, e) = (s, translate_pure empty_env e) in
  (* introduce the type of states *)
(*   intro_state_type (); *)
  (* then translate *)
  (* translate the code *)
  { c_types = table.d_types;
    c_code = List.map translate table.d_code;
    c_vars = table.d_vars;
  }
