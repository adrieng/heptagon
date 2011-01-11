(**************************************************************************)
(*                                                                        *)
(*  Lucid Synchrone                                                       *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* $Id: declarative.ml,v 1.18 2007-01-11 07:35:53 pouzet Exp $ *)
(* the intermediate format *)

open Misc
open Names

(* one set of (unique) names *)
type name = int

type global =
    Gname of string * name
  | Gmodname of qualified_ident

(* type definitions *)
type type_definition =
    { d_type_desc: type_components;
      d_type_arity: int list
    }

and ('a, 'b) ptyp = { arg: 'a; res: 'b }

and type_components =
    Dabstract_type
  | Dabbrev of typ
  | Dvariant_type of (qualified_ident * (typ list, typ) ptyp) list
  | Drecord_type of (qualified_ident * is_mutable * (typ, typ) ptyp) list

and is_mutable = bool

(* types *)
and typs = Dtypforall of name list * typ
and typ =
  | Darrow of is_node * typ * typ
  | Dproduct of typ list
  | Dconstr of qualified_ident * typ list
  | Dtypvar of name
  | Dbase of base_typ
  | Dsignal of typ

and is_node = bool

and base_typ =
    Dtyp_bool | Dtyp_int | Dtyp_float | Dtyp_unit |
    Dtyp_char | Dtyp_string

type guard = clock

and clock =
  | Dfalse                         (* the false clock *)
  | Dtrue                          (* the base clock *)
  | Don of bool * clock * carrier  (* "cl on c" or "cl on not c" *)
  | Dclockvar of name              (* 'a *)

and carrier =
    Dcfalse
  | Dctrue
  | Dcvar of name
  | Dcglobal of qualified_ident * name option * clock
                                   (* identifier, reset name and clock *)

(* immediate values *)
type immediate =
  | Dbool of bool
  | Dint of int
  | Dfloat of float
  | Dchar of char
  | Dstring of string
  | Dvoid

type 'a desc =
    { d_desc: 'a;
      d_ty: typ;
      d_guard: guard
    }

(* patterns *)
type pattern =
  | Dwildpat
  | Dvarpat of name
  | Dconstantpat of immediate
  | Dtuplepat of pattern list
  | Dconstructpat of qualified_ident * pattern list
  | Drecordpat of (qualified_ident * pattern) list
  | Daliaspat of pattern * name
  | Dorpat of pattern * pattern

(* signal expressions *)
type spattern =
  | Dandpat of spattern * spattern
  | Dexppat of expr
  | Dcondpat of expr * pattern

(* expressions *)
and expr = expr_desc desc

and expr_desc =
  | Dconstant of immediate
  | Dvar of var * subst
  | Dlast of name
  | Dpre of expr option * expr
  | Difthenelse of expr * expr * expr
  | Dinit of clock * name option
  | Dtuple of expr list
  | Dconstruct of qualified_ident * expr list
  | Drecord of (qualified_ident * expr) list
  | Drecord_access of expr * qualified_ident
  | Dprim of qualified_ident * expr list
  | Dfun of is_state * params * pattern list * block * expr
  | Dapply of is_state * expr * expr list
  | Dlet of block * expr
  | Deseq of expr * expr
  | Dtest of expr (* testing the presence "?" *)
  | Dwhen of expr (* instruction "when" *)
  | Dclock of clock

and is_state = bool

and var =
  | Dlocal of name
  | Dglobal of qualified_ident

and is_external = bool (* true for imported ML values *)

(* type and clock instance *)
and ('a, 'b, 'c) substitution =
    { s_typ: 'a list;
      s_clock: 'b list;
      s_carrier: 'c list }

and subst = (typ, clock, carrier) substitution
and params = (name, name, name) substitution

(* block *)
and block =
    { b_env: (name, ident) Hashtbl.t;   (* environment *)
      mutable b_write: name list;       (* write variables *)
      b_equations: equation;            (* equations *)
    }

(* equation *)
and equation =
    Dequation of pattern * expr             (* equation p = e *)
  | Dnext of name * expr                    (* next x = e *)
  | Dlasteq of name * expr                  (* last x = e *)
  | Demit of pattern * expr                 (* emit pat = e *)
  | Dstatic of pattern * expr               (* static pat = e *)
  | Dget of pattern * var                   (* pat = x *)
  | Dwheneq of equation * guard             (* eq when clk *)
  | Dmerge of is_static * expr              (* control structure *)
        * (pattern * block) list
  | Dreset of equation * expr               (* reset *)
  | Dautomaton of clock * (state_pat * block * block * escape * escape) list
                                            (* automaton weak and strong *)
  | Dpar of equation list                   (* parallel equations *)
  | Dseq of equation list                   (* sequential equations *)
  | Dblock of block                         (* block structure *)
  | Dpresent of clock * (spattern * block) list * block
                                            (* presence testing *)

and escape = (spattern * block * is_continue * state) list

and is_static = bool
and is_strong = bool
and is_continue = bool

and state_pat = string * pattern list
and state = string * expr list

(* ident definition *)
and ident =
    { id_name: name;              (* its name (unique identifier) *)
      id_original: string option; (* its original name when possible *)
      id_typ: typs;               (* its type *)
      id_value: expr option;      (* its initial value when possible *)
      mutable id_kind: id_kind;   (* kind of identifier *)
      mutable id_write: bool;     (* physically assigned or not *)
      mutable id_last: bool;      (* do we need its last value also? *)
      mutable id_signal: bool;    (* is-it a signal? *)
    }

(* a local variable in a block may be of four different kinds *)
and id_kind =
    Kinit   (* initialisation state variable *)
  | Kclock  (* clock variable *)
  | Kreset  (* reset variable *)
  | Kmemo   (* state variable *)
  | Kstatic (* static variable *)
  | Klast   (* last variable *)
  | Kvalue  (* defined variable *)
  | Kshared (* shared variable with several definitions *)
  | Kinput  (* input variable, i.e, argument *)

(* global definition *)
(* Invariant: expr must be bounded and static *)

(* the declarative code associated to a file *)
type declarative_code =
    { mutable d_modname: string;                 (* module name *)
      mutable d_types: (string, type_definition) Hashtbl.t;
                                                 (* type definitions *)
      mutable d_code: (string * expr) list;      (* value definitions *)
      mutable d_vars: string list;               (* defined names     *)
    }


(* the generated code of a module *)
let dc = { d_modname = "";
     d_types = Hashtbl.create 7;
     d_code = [];
     d_vars = []
   }

let code () = dc

(* thing to do when starting the production of declarative code *)
(* for a file *)
let start modname =
  dc.d_modname <- modname;
  dc.d_types <- Hashtbl.create 7;
  dc.d_code <- [];
  dc.d_vars <- []

(* things to do at the end of the front-end*)
let finish () =
  dc.d_code <- List.rev dc.d_code

(* apply a function to every value *)
let replace translate =
  let rec replace (s, e) =
    let e = translate e in
      dc.d_code <- (s, e) :: dc.d_code in
  let code = dc.d_code in
  dc.d_code <- [];
  List.iter replace code;
  dc.d_code <- List.rev dc.d_code


(* add an input to the declarative code *)
let add_dec (name, code) =
  dc.d_code <- (name, code) :: dc.d_code;
  dc.d_vars <- name :: dc.d_vars

(* add a type definition to the declarative code *)
let add_type (name, type_def) =
  Hashtbl.add dc.d_types name type_def

(* read code from and write code into a file *)
let read_declarative_code ic = input_value ic

let write_declarative_code oc =
  output_value oc (code ())

(* the list of opened modules *)
let dc_modules = (Hashtbl.create 7 : (string, declarative_code) Hashtbl.t)

(* add a module to the list of opened modules *)
let add_module m =
  let name = String.uncapitalize m in
    try
      let fullname = find_in_path (name ^ ".dcc") in
      let ic = open_in fullname in
      let dc = input_value ic in
  Hashtbl.add dc_modules m dc;
  close_in ic;
  dc
    with
  Cannot_find_file _ ->
    Printf.eprintf
      "Cannot find the compiled declarative file %s.dcc.\n"
      name;
    raise Error

let find_value qualid =
  let dc =
    if qualid.qual = dc.d_modname then dc
    else raise Not_found
(*
      try
  Hashtbl.find dc_modules qualid.qual
      with
    Not_found -> add_module qualid.qual *) in
    List.assoc qualid.id dc.d_code

let find_type qualid =
  if qualid.qual = dc.d_modname then Hashtbl.find dc.d_types qualid.qual
  else raise Not_found
