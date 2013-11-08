(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(* Nicolas Berthier, SUMO, INRIA                                       *)
(*                                                                     *)
(* Copyright 2013 ENS, INRIA, UJF                                      *)
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

(** Controllable-Nbac representation and output module

    @author Nicolas Berthier *)

(* -------------------------------------------------------------------------- *)

(** Variable names *)
type var = Names.name

(** Module for variable mappings *)
module VMap = Names.NamesEnv

(** Module for variable sets *)
module VSet = Names.NamesSet

(** User-defined type names *)
type typname = Names.name

(** Enumaration labels *)
type label = string

(** Enumeration type definition *)
type typdef =
  | EnumDef of label list

(** Collection of enumeration type definitions *)
type typdefs = typdef VMap.t

(** Numerical types *)
type ntyp = [ `Int | `Real ]

(** All handled types *)
type typ = [ `Bool | `Enum of typname | ntyp ]

(* -------------------------------------------------------------------------- *)
(* {3 Expressions} *)

(** Equivalence relation operators *)
type eqrel = [ `Eq | `Ne ]

(** Total ordering relation operators *)
type totrel = [ eqrel | `Lt | `Le | `Gt | `Ge ]

(** Boolean unary operator *)
type buop = [ `Neg ]

(** Boolean nary operators. [`Excl] denotes {e mutual exclusion} between all its
    arguments. *)
type bnop = [ `Conj | `Disj | `Excl ]

(** Numerical unary operator *)
type nuop = [ `Opp ]

(** Numerical nary operators *)
type nnop = [ `Add | `Sub | `Mul | `Div ]

(** Polymorphic conditional operator *)
type ('t, 'b) cond = [ `Ite of 'b * 't * 't ]

(** Numerical expressions *)
type nexp =
  [
  | `Ref of var
  | `Int of int
  | `Real of float
  | `Nuop of nuop * nexp
  | `Nnop of nnop * nexp * nexp * nexp list           (** (>=2)-ary operations *)
  | ('a, bexp) cond
  ] as 'a

(** Enumeration expressions *)
and eexp =
  [
  | `Ref of var
  | `Enum of label
  | ('a, bexp) cond
  ] as 'a

(** Boolean expressions *)
and bexp =
  [
  | `Ref of var
  | `Bool of bool
  | `Buop of buop * bexp
  | `Bnop of bnop * bexp * bexp * bexp list           (** (>=2)-ary operations *)
  | `Bcmp of eqrel * bexp * bexp
  | `Ncmp of totrel * nexp * nexp
  | `Ecmp of eqrel * eexp * eexp
  | `Ein of eexp * label * label list                   (** at least one label *)
  | ('a, bexp) cond
  ] as 'a

(** Untyped expressions *)
type exp =
  [
  | `Bexp of bexp
  | `Eexp of eexp
  | `Nexp of nexp
  ]

(* -------------------------------------------------------------------------- *)
(* {3 Nodes & Programs} *)

(** Rank of controllable inputs *)
type rank = int

(** All kinds of variable specifications *)
type var_spec =
  | NBstate of exp       (** state variables define the transition function *)
  | NBinput              (** input *)
  | NBcontr of rank      (** controllables have a {e unique} rank (not checked) *)
  | NBlocal of exp       (** local definitions *)

(** Variable declarations combine a type with a specification. Note that the
    conformance between the declared type and any expression in the
    specification is not checked. *)
type var_decl = typ * var_spec

(** Sets of variable declarations. *)
type decls = var_decl VMap.t

(** Controllable-nbac process (aka: node). Note the initial state specification
    may not define all values of the state variables. *)
type process =
    {
      cn_name: Names.name;           (** node name *)
      cn_decls: decls;               (** all variable specifications *)
      cn_init: bexp;                 (** initial state specification *)
      cn_assertion: bexp;            (** assertion on environment *)
      cn_invariance: bexp option;    (** {e invariance} property to enforce *)
      cn_reachability: bexp option;  (** {e reachability} property to enforce *)
    }

(** A whole controllable-nbac program contains type definitions and
    processes. *)
type prog =
    {
      cnp_name: Names.name;
      cnp_typs: typdefs;
      cnp_procs: process list;
    }

(* -------------------------------------------------------------------------- *)
(* {2 Utilities} *)

(** Building variables *)
let mk_var s = s

(** Prefixing variables with a string. *)
let (^~) = Printf.sprintf "%s%s"

(* -------------------------------------------------------------------------- *)
(* {3 Gathering process info} *)

(** Type of data returned by {!gather_info} *)
type process_infos =
    {
      cni_state_vars: typ VMap.t;          (** state variable declarations *)
      cni_input_vars: typ VMap.t;          (** input variable declarations *)
      cni_contr_vars: (typ * rank) VMap.t; (** controllable variable decls *)
      cni_contr_vars': (var * typ) list;   (** ordered controllable variables *)
      cni_local_vars: typ VMap.t;          (** local variable declarations *)
      cni_local_specs: exp VMap.t;         (** local variable definitions *)
      cni_trans_specs: exp VMap.t;         (** state variable definitions *)
    }

(** [gather_info process] computes data structures suitable for fast retrieval
    of various information about [process]. *)
let gather_info { cn_decls } =
  let empty = VMap.empty in
  let s, i, c, l, d, f = VMap.fold begin fun v -> function
    | t, NBstate e -> fun (s,i,c,l,d,f) -> (VMap.add v t s,i,c,l, d,VMap.add v e f)
    | t, NBlocal e -> fun (s,i,c,l,d,f) -> (s,i,c,VMap.add v t l, VMap.add v e d,f)
    | t, NBinput   -> fun (s,i,c,l,d,f) -> (s,VMap.add v t i,c,l, d,f)
    | t, NBcontr p -> fun (s,i,c,l,d,f) -> (s,i,VMap.add v (t,p) c,l, d,f)
  end cn_decls (empty, empty, empty, empty, empty, empty) in
  let cl = VMap.bindings c in
  let cl = List.sort (fun (_, (_, a)) (_, (_, b)) -> compare a b) cl in
  let cl = List.map (fun (v, (t, _)) -> (v, t)) cl in            (* forger rank *)
  { cni_state_vars = s;
    cni_input_vars = i;
    cni_contr_vars = c; cni_contr_vars' = cl;
    cni_local_vars = l;
    cni_local_specs = d;
    cni_trans_specs = f; }

(* -------------------------------------------------------------------------- *)
(* {3 Building and declaring enumerations} *)

(** Empty set of type definitions *)
let empty_typdefs: typdefs = VMap.empty

(** Adds a type definition into the given set. Any type previously defined with
    the same name is removed. *)
let declare_typ: typname -> typdef -> typdefs -> typdefs = VMap.add

(** Builds a type name; enforces compatibility with Nbac format. *)
let mk_typname: Names.name -> typname = String.capitalize

(** Builds a label; enforces compatibility with Nbac format. *)
let mk_label: Names.name -> label = String.capitalize

(** Builds an enumeration type definition *)
let mk_etyp: label list -> typdef = fun l -> EnumDef l

(* -------------------------------------------------------------------------- *)
(* {3 Building expressions} *)

(** Exception raised when an invalid expression is given to the non-primed
    functions bellow. *)
exception TypeError of string

let as_bexp: exp -> bexp = function
  | `Bexp e -> e
  | _ -> raise (TypeError "Boolean expression expected!")

let as_eexp: exp -> eexp = function
  | `Eexp e -> e
  | _ -> raise (TypeError "Enumeration expression expected!")

let as_nexp: exp -> nexp = function
  | `Nexp e -> e
  | _ -> raise (TypeError "Numerical expression expected")

type bexp' = [ `Bexp of bexp ]
and eexp' = [ `Eexp of eexp ]
and nexp' = [ `Nexp of nexp ]
(** [bexp'], [eexp'] and [nexp'] are alias types for shortening signatures;
    recall that a type [[> t]] can be coerced into a larger one without further
    annotations ({i e.g.}, the result of [(mk_bref v)] can be used directly as
    if it were of type {!exp}). *)

let mk_bref' v :> bexp = `Ref v
let mk_bcst' c :> bexp = `Bool c

let mk_neg': bexp -> bexp = function
  | `Buop (`Neg, e) -> e
  | e -> `Buop (`Neg, e)

let mk_and': bexp -> bexp -> bexp =
  let rec conj leaf a = function
    | `Bool true -> a
    | `Bool false as b -> b
    | `Bnop (`Conj, e, f, l) as b -> (match a with
        | `Bnop (`Conj, e', f', l') -> `Bnop (`Conj, e, f, e' :: f' :: l @ l')
        | a when leaf -> `Bnop (`Conj, e, f, a :: l)
        | a -> conj true b a)
    | b when leaf -> `Bnop (`Conj, b, a, [])
    | b -> conj true b a
  in
  conj false

let mk_or': bexp -> bexp -> bexp =
  let rec disj leaf a = function
    | `Bool true as b -> b
    | `Bool false -> a
    | `Bnop (`Disj, e, f, l) as b -> (match a with
        | `Bnop (`Disj, e', f', l') -> `Bnop (`Disj, e, f, e' :: f' :: l @ l')
        | a when leaf -> `Bnop (`Disj, e, f, a :: l)
        | a -> disj true b a)
    | b when leaf -> `Bnop (`Disj, b, a, [])
    | b -> disj true b a
  in
  disj false

let mk_xor': bexp -> bexp -> bexp = fun a b -> `Bnop (`Excl, a, b, [])

(**/**)

let _mk_bcmp': eqrel -> bexp -> bexp -> bexp = fun op a b -> match op, a, b with
  | `Eq, `Bool true, b  | `Ne, `Bool false, b -> b
  | `Eq, `Bool false, b | `Ne, `Bool true, b  -> mk_neg' b
  | `Eq, a, `Bool true  | `Ne, a, `Bool false -> a
  | `Eq, a, `Bool false | `Ne, a, `Bool true  -> mk_neg' a
  | op, a, b -> `Bcmp (op, a, b)
let _mk_ecmp': eqrel -> eexp -> eexp -> bexp = fun op a b -> `Ecmp (op, a, b)
let _mk_ncmp': totrel -> nexp -> nexp -> bexp = fun op a b -> `Ncmp (op, a, b)

let _mk ~bexp ~eexp ~nexp x y = match x, y with
  | `Bexp x, `Bexp y -> bexp x y
  | `Eexp x, `Eexp y -> eexp x y
  | `Nexp x, `Nexp y -> nexp x y
  | _ -> raise (TypeError "Type mismatch!")

let _mk_bnary' a1 an e = function
  | [] -> a1 e
  | f :: l -> an e f l

let _mk_bnary filter a1 an e el =
  _mk_bnary' a1 an (filter e) (List.rev_map filter el)

let _mk_nary' filter an e f el = an (filter e) (filter f) (List.map filter el)

(**/**)

let mk_conj': bexp -> bexp list -> bexp = _mk_bnary'
  (fun e -> e) (fun e f l -> List.fold_left mk_and' (mk_and' e f) l)
let mk_disj': bexp -> bexp list -> bexp = _mk_bnary'
  (fun e -> e) (fun e f l -> List.fold_left mk_or' (mk_or' e f) l)
let mk_excl': bexp -> bexp list -> bexp = _mk_bnary'
  (fun e -> e) (fun e f l -> `Bnop (`Excl, e, f, l))

let mk_ein': eexp -> label -> label list -> bexp = fun e l ll -> `Ein (e, l, ll)

let mk_beq' = _mk_bcmp' `Eq and mk_eeq' = _mk_ecmp' `Eq
and mk_neq' = _mk_ncmp' `Eq
and mk_bne' = _mk_bcmp' `Ne and mk_ene' = _mk_ecmp' `Ne
and mk_nne' = _mk_ncmp' `Ne
and mk_lt'  = _mk_ncmp' `Lt and mk_le'  = _mk_ncmp' `Le
and mk_gt'  = _mk_ncmp' `Gt and mk_ge'  = _mk_ncmp' `Ge

let mk_eref' v :> eexp = `Ref v
let mk_ecst' l :> eexp = `Enum l

let mk_nref' v :> nexp = `Ref v
let mk_nicst' i :> nexp = `Int i
let mk_nrcst' f :> nexp = `Real f

let _mk_nnop': nnop -> nexp -> nexp -> nexp list -> nexp = fun op e f l ->
  `Nnop (op, e, f, l)
let mk_add' = _mk_nnop' `Add and mk_sub' = _mk_nnop' `Sub
and mk_mul' = _mk_nnop' `Mul and mk_div' = _mk_nnop' `Div

(** Conditional operator, to be used with enumeration and numerical
    expressions. *)
let mk_cond': bexp -> ([> `Ite of bexp * 'a * 'a ] as 'a) -> 'a -> 'a = function
  | `Bool true -> fun t _e -> t
  | `Bool false -> fun _t e -> e
  | c -> fun t e -> `Ite (c, t, e)

(** Conditional operator constructor, specialized for Boolean expressions. *)
let mk_bcond': bexp -> bexp -> bexp -> bexp = function
  | `Bool true -> fun t _e -> t
  | `Bool false -> fun _t e -> e
  | c -> fun t e -> match t, e with
      | `Bool true, `Bool false -> c
      | `Bool false, `Bool true -> mk_neg' c
      | t, e -> `Ite (c, t, e)

(* --- *)

let mk_bref v :> [> bexp' ] = `Bexp (mk_bref' v)
let mk_bcst c :> [> bexp' ] = `Bexp (mk_bcst' c)

let mk_neg e : [> bexp' ] = `Bexp (mk_neg' (as_bexp e))
let mk_and a b : [> bexp' ] = `Bexp (mk_and' (as_bexp a) (as_bexp b))
let mk_or a b : [> bexp' ] = `Bexp (mk_or' (as_bexp a) (as_bexp b))
let mk_xor a b : [> bexp' ] = `Bexp (mk_xor' (as_bexp a) (as_bexp b))

let mk_conj: exp -> exp list -> [> bexp' ] = _mk_bnary as_bexp
  (fun e -> `Bexp e) (fun e f l -> `Bexp (List.fold_left mk_and' (mk_and' e f) l))
let mk_disj: exp -> exp list -> [> bexp' ] = _mk_bnary as_bexp
  (fun e -> `Bexp e) (fun e f l -> `Bexp (List.fold_left mk_or' (mk_or' e f) l))
let mk_excl: exp -> exp list -> [> bexp' ] = _mk_bnary as_bexp
  (fun e -> `Bexp e) (fun e f l -> `Bexp (mk_excl' e (f::l)))

let mk_ein: exp -> label -> label list -> [> bexp' ] = fun e l ll ->
  `Bexp (mk_ein' (as_eexp e) l ll)

let _mk_cmp: eqrel -> exp -> exp -> [> bexp' ] = fun op -> _mk
  ~bexp:(fun a b -> `Bexp (_mk_bcmp' op a b))
  ~eexp:(fun a b -> `Bexp (_mk_ecmp' op a b))
  ~nexp:(fun a b -> `Bexp (_mk_ncmp' (op :> totrel) a b))
let mk_eq = _mk_cmp `Eq  and mk_ne = _mk_cmp `Ne

let _mk_ncmp: totrel -> exp -> exp -> [> bexp' ] = fun op a b ->
  `Bexp (_mk_ncmp' op (as_nexp a) (as_nexp b) :> bexp)
let mk_lt = _mk_ncmp `Lt and mk_le = _mk_ncmp `Le
and mk_gt = _mk_ncmp `Gt and mk_ge = _mk_ncmp `Ge

(* --- *)

let mk_eref v : [> eexp' ] = `Eexp (mk_eref' v)
and mk_ecst l : [> eexp' ] = `Eexp (mk_ecst' l)

let mk_nref v : [> nexp' ] = `Nexp (mk_nref' v)
and mk_nicst i : [> nexp' ] = `Nexp (mk_nicst' i)
and mk_nrcst f : [> nexp' ] = `Nexp (mk_nrcst' f)

(* --- *)

let _mk_nnop: nnop -> exp -> exp -> exp list -> [> nexp' ] = fun op ->
  _mk_nary' as_nexp (fun e f l -> `Nexp (_mk_nnop' op e f l))
let mk_add = _mk_nnop `Add and mk_sub = _mk_nnop `Sub
and mk_mul = _mk_nnop `Mul and mk_div = _mk_nnop `Div

(* --- *)

let mk_condb: bexp -> exp -> exp -> exp = fun c -> _mk
  ~bexp:(fun a b -> `Bexp (mk_bcond' c a b))
  ~eexp:(fun a b -> `Eexp (mk_cond' c a b))
  ~nexp:(fun a b -> `Nexp (mk_cond' c a b))

let mk_cond c = mk_condb (as_bexp c)

(* -------------------------------------------------------------------------- *)
(* {3 Pretty-printing} *)

(** Module for dumping Controllable-Nbac programs. *)
module Printer = struct

  open Format

  (**/**)

  let peqrel = function
    | `Eq -> " = "
    | `Ne -> " <> "
  let ptotrel = function
    | #eqrel as op -> peqrel op
    | `Lt -> " < " | `Le -> " <= "
    | `Gt -> " > " | `Ge -> " >= "

  let ps = pp_print_string
  let pv = ps                                     (* XXX Names.print_name (?) *)

  let pcond pb p' fmt = function
    | `Ite (b, e, f) ->
        fprintf fmt "(if@ @[%a@]@ then@ @[%a@]@ else@ @[%a@])" pb b p' e p' f

  (** Pretty-printing types. *)

  let print_typ fmt = function
    | `Bool -> ps fmt "bool"
    | `Int -> ps fmt "int"
    | `Real -> ps fmt "real"
    | `Enum tn -> ps fmt tn

  let rec pb fmt : bexp -> unit = function
    | `Ref v -> pv fmt v
    | `Bool b -> fprintf fmt "%b" b
    | `Buop (`Neg,`Ref v) -> fprintf fmt "not %a" pv v
    | `Buop (`Neg,e) -> fprintf fmt "not (%a)" pb e
    | `Bnop (`Conj,e,f,l) -> Pp_tools.print_list_r pb "" " and" "" fmt (e::f::l)
    | `Bnop (`Disj,e,f,l) -> Pp_tools.print_list_r pb "(" " or" ")" fmt (e::f::l)
    | `Bnop (`Excl,e,f,l) -> Pp_tools.print_list_r pb "#(" "," ")" fmt (e::f::l)
    | `Bcmp (cmp,e,f) -> fprintf fmt "(%a%s%a)" pb e (peqrel cmp) pb f
    | `Ncmp (cmp,i,j) -> fprintf fmt "(%a%s%a)" pn i (ptotrel cmp) pn j
    | `Ecmp (cmp,e,f) -> fprintf fmt "(%a%s%a)" pe e (peqrel cmp) pe f
    | `Ein (e, l, l') ->(fprintf fmt "%a in %a" pe e
                          (Pp_tools.print_list_r pv "{" "," "}") (l::l'))
    | #cond as c -> pcond pb pb fmt c
  and pe fmt : eexp -> unit = function
    | `Ref v -> pv fmt v
    | `Enum s -> pv fmt s
    | #cond as c -> pcond pb pe fmt c
  and pn fmt : nexp -> unit = function
    | `Ref v -> pv fmt v
    | `Int i -> fprintf fmt "%d" i
    | `Real f -> fprintf fmt "%f" f
    | `Nuop (`Opp,`Ref v) -> fprintf fmt "- %a" pv v
    | `Nuop (`Opp,e) -> fprintf fmt "- (%a)" pn e
    | `Nnop (`Add,e,f,l) -> Pp_tools.print_list_r pn "(" " +" ")" fmt (e::f::l)
    | `Nnop (`Sub,e,f,l) -> Pp_tools.print_list_r pn "(" " -" ")" fmt (e::f::l)
    | `Nnop (`Mul,e,f,l) -> Pp_tools.print_list_r pn "" " *" "" fmt (e::f::l)
    | `Nnop (`Div,e,f,l) -> Pp_tools.print_list_r pn "" " /" "" fmt (e::f::l)
    | #cond as c -> pcond pb pn fmt c

  (**/**)

  let print_var = pv

  let print_typdef f : typdef -> unit = function
    | EnumDef labels -> Pp_tools.print_list ps "{" "," "}" f labels

  let print_typdefs f = VMap.iter (fun tn ->
    fprintf f "%s = enum @[%a@];@\n" tn print_typdef)

  let print_bexp = pb
  and print_eexp = pe
  and print_nexp = pn
  and print_exp fmt : exp -> unit = function
    | `Bexp b -> pb fmt b
    | `Eexp e -> pe fmt e
    | `Nexp n -> pn fmt n

  (**/**)

  let print_decls f = VMap.iter (fun v -> fprintf f "%s: %a;@\n" v print_typ)
  let print_decll f = List.iter (fun (v,t) -> fprintf f "%s: %a;@\n" v print_typ t)
  let print_defs f = VMap.iter (fun v -> fprintf f "%s = @[%a@];@\n" v print_exp)
  let print_trans f = VMap.iter (fun v -> fprintf f "%s'= @[%a@];@\n" v print_exp)
  let print_predicate f = fprintf f "%a;" pb

  let print_cat f = fprintf f "%s@\n  @[%a@]@\n"
  let print_cat' f n p m = if not (VMap.is_empty m) then print_cat f n p m
  let print_cal' f n p l = if l <> [] then print_cat f n p l
  let print_cao' f n p = function | None -> () | Some e -> print_cat f n p e

  (**/**)

  let print_proc fmt process =
    let pi = gather_info process in
    print_cat  fmt "state" print_decls pi.cni_state_vars;
    print_cat' fmt "input" print_decls pi.cni_input_vars;
    print_cal' fmt "controllable" print_decll pi.cni_contr_vars';
    print_cat' fmt "local" print_decls pi.cni_local_vars;
    print_cat' fmt "definition" print_defs pi.cni_local_specs;
    print_cat  fmt "transition" print_trans pi.cni_trans_specs;
    print_cat  fmt "initial" print_predicate process.cn_init;
    print_cat  fmt "assertion" print_predicate process.cn_assertion;
    print_cao' fmt "invariant" print_predicate process.cn_invariance;
    print_cao' fmt "reachable" print_predicate process.cn_reachability

  (** [dumps mk_fmt p] dumps separately each process of program [p] in
      formatters produced calling [mk_fmt] with the process's name. The latter
      function returns a couple gathering the formatter and a procedure to
      release any attached resources ({i e.g}, to close output channels). *)
  let dump mk_fmt { cnp_typs = typs; cnp_procs } =
    List.iter begin fun ({ cn_name = name } as proc) ->
      let fmt, release = mk_fmt name in
      Compiler_utils.print_header_info fmt "(*" "*)";
      print_cat' fmt "typedef" print_typdefs typs;
      print_proc fmt proc;
      release fmt;
    end cnp_procs

end;;

(* -------------------------------------------------------------------------- *)
