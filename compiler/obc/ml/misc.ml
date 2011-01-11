(**************************************************************************)
(*                                                                        *)
(*  Lucid Synchrone                                                       *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* $Id: misc.ml,v 1.11 2006-09-30 12:27:27 pouzet Exp $ *)

(* version of the compiler *)
let version = "3.0b"

let date = DATE

(* standard module *)
let pervasives_module = "Pervasives"
let standard_lib = STDLIB

(* variable creation *)
(* generating names *)
class name_generator =
  object
    val mutable counter = 0
    method name =
      counter <- counter + 1;
      counter
    method reset =
      counter <- 0
    method init i =
      counter <- i
  end

(* association table with memoization *)
class name_assoc_table f =
  object
    val mutable counter = 0
    val mutable assoc_table: (int * string) list = []
    method name var =
      try
  List.assq var assoc_table
      with
  not_found ->
    let n = f counter in
    counter <- counter + 1;
    assoc_table <- (var,n) :: assoc_table;
    n
    method reset =
      counter <- 0;
      assoc_table <- []
  end

(* error during the whole process *)
exception Error

(* internal error : for example, an abnormal pattern matching failure *)
(* gives the name of the function *)
exception Internal_error of string

let fatal_error s = raise (Internal_error s)

let not_yet_implemented s =
  Printf.eprintf "The construction %s is not implemented yet.\n" s;
  raise Error

(* creating a name generator for type and clock calculus *)
(* ensure unicity for the whole process *)
let symbol = new name_generator

(* generic and non generic variables in the various type systems *)
let generic = -1
let notgeneric = 0
let maxlevel = max_int

let binding_level = ref 0
let top_binding_level () = !binding_level = 0

let push_binding_level () = binding_level := !binding_level + 1
let pop_binding_level () =
  binding_level := !binding_level - 1;
  assert (!binding_level > generic)
let reset_binding_level () = binding_level := 0

(* realtime mode *)
let realtime = ref false

(* assertions *)
let no_assert = ref false

(* converting integers into variable names *)
(* variables are printed 'a, 'b *)
let int_to_letter bound i =
  if i < 26
  then String.make 1 (Char.chr (i+bound))
  else String.make 1 (Char.chr ((i mod 26) + bound)) ^ string_of_int (i/26)

let int_to_alpha i = int_to_letter 97 i

(* printing information *)
class on_off =
  object
    val mutable status = false
    method set = status <- true
    method get = status
  end

let print_type = new on_off
let print_clock = new on_off
let print_init = new on_off
let print_causality = new on_off
let no_causality = ref false
let no_initialisation = ref false

let no_deadcode = ref false

(* control what is done in the compiler *)
exception Stop

let only = ref ""
let set_only_info o = only := o
let parse_only () =
  if !only = "parse" then raise Stop
let type_only () =
  if !only = "type" then raise Stop
let clock_only () =
  if !only = "clock" then raise Stop
let caus_only () =
  if !only = "caus" then raise Stop
let init_only () =
  if !only = "init" then raise Stop
let dec_only () =
  if !only = "parse" or !only = "type"
  or !only = "clock" or !only = "init"
  or !only = "dec" then raise Stop

(* load paths *)
let load_path = ref ([] : string list)

(* no link *)
let no_link = ref false

(* simulation node *)
let simulation_node = ref ""

(* sampling rate *)
let sampling_rate : int option ref = ref None

(* level of inlining *)
let inlining_level = ref 10

(* emiting declarative code *)
let print_declarative_code = ref false
let print_auto_declarative_code = ref false
let print_total_declarative_code = ref false
let print_last_declarative_code = ref false
let print_signals_declarative_code = ref false
let print_reset_declarative_code = ref false
let print_linearise_declarative_code = ref false
let print_initialize_declarative_code = ref false
let print_split_declarative_code = ref false
let print_inline_declarative_code = ref false
let print_constant_declarative_code = ref false
let print_deadcode_declarative_code = ref false
let print_copt_declarative_code = ref false

(* total emission of signals *)
let set_total_emit = ref false

(* generating C *)
let make_c_code = ref false

(* profiling information about the compilation *)
let print_exec_time = ref false

exception Cannot_find_file of string

let find_in_path filename =
  if Sys.file_exists filename then
    filename
  else if not(Filename.is_implicit filename) then
    raise(Cannot_find_file filename)
  else
    let rec find = function
      [] ->
        raise(Cannot_find_file filename)
    | a::rest ->
        let b = Filename.concat a filename in
          if Sys.file_exists b then b else find rest
    in find !load_path


(* Prompts: [error_prompt] is printed before compiler error *)
(*          and warning messages *)
let error_prompt = ">"

(* list intersection *)
let intersect l1 l2 =
  List.exists (fun el -> List.mem el l1) l2

(* remove an entry from an association list *)
let rec remove n l =
  match l with
    [] -> raise Not_found
  | (m, v) :: l ->
      if n = m then l else (m, v) :: remove n l

(* list substraction. l1 - l2 *)
let sub_list l1 l2 =
  let rec sl l l1 =
    match l1 with
      [] -> l
    | h :: t -> sl (if List.mem h l2 then l else (h :: l)) t in
  sl [] l1

(* union *)
let rec union l1 l2 =
  match l1, l2 with
    [], l2 -> l2
  | l1, [] -> l1
  | x :: l1, l2 ->
      if List.mem x l2 then union l1 l2 else x :: union l1 l2

let addq x l = if List.memq x l then l else x :: l

let rec unionq l1 l2 =
  match l1, l2 with
    [], l2 -> l2
  | l1, [] -> l1
  | x :: l1, l2 ->
      if List.memq x l2 then unionq l1 l2 else x :: unionq l1 l2

(* intersection *)
let rec intersection l1 l2 =
  match l1, l2 with
    ([], _) | (_, []) -> []
  | x :: l1, l2 -> if List.mem x l2 then x :: intersection l1 l2
                   else intersection l1 l2

(* the last element of a list *)
let rec last l =
  match l with
    [] -> raise (Failure "last")
  | [x] -> x
  | _ :: l -> last l

(* iterator *)
let rec map_fold f acc l =
  match l with
    [] -> acc, []
  | x :: l ->
      let acc, v = f acc x in
      let acc, l = map_fold f acc l in
      acc, v :: l

(* flat *)
let rec flat l =
  match l with
    [] -> []
  | x :: l -> x @ flat l

(* reverse *)
let reverse l =
  let rec reverse acc l =
    match l with
      [] -> acc
    | x :: l -> reverse (x :: acc) l in
  reverse [] l

(* generic printing of a list *)
let print_list print print_sep l =
  let rec printrec l =
    match l with
      [] -> ()
    | [x] ->
  print x
    | x::l ->
  print x;
  print_sep ();
  printrec l in
  printrec l

(* generates the sequence of integers *)
let rec from n = if n = 0 then [] else n :: from (n-1)

(* for infix operators, print parenthesis around *)
let is_an_infix_or_prefix_operator op =
  if op = "" then false
  else
    let c = String.get op 0 in
    not (((c >= 'a') & (c <= 'z')) or ((c >= 'A') & (c <= 'Z')))

(* making a list from a hash-table *)
let listoftable t =
  Hashtbl.fold (fun key value l -> (key, value) :: l) t []
