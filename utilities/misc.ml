(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* useful stuff *)
(* $Id$ *)

(* version of the compiler *)
let version = "0.4"
let interface_format_version = "5"
let date = "DATE"

(* standard module *)
let pervasives_module = "Pervasives"
let standard_lib = "STDLIB"
let standard_lib = try Sys.getenv "HEPTLIB" with Not_found -> standard_lib

(* list of modules initially opened *)
let default_used_modules = ref [pervasives_module]
let set_no_pervasives () = default_used_modules := []

(* load paths *)
let load_path = ref ([standard_lib])

let set_stdlib p =
  load_path := [p]
and add_include d =
  load_path := d :: !load_path;;

(* where is the standard library *)
let locate_stdlib () =
  let stdlib = try
    Sys.getenv "HEPTLIB"
  with
    Not_found -> standard_lib in
  Printf.printf "Standard library in %s\n" stdlib

let show_version () =
  Printf.printf "The Heptagon compiler, version %s (%s)\n"
    version date;
  locate_stdlib ()

(* other options of the compiler *)
let verbose = ref false
let print_types = ref false

let simulation = ref false
let simulation_node : string option ref = ref None
let set_simulation_node s =
  simulation := true;
  simulation_node := Some s

(* Target languages list for code generation *)
let target_languages : string list ref = ref []

let add_target_language s =
  target_languages := s :: !target_languages

(* Optional path for generated files (C or Java) *)
let target_path : string option ref = ref None

let set_target_path path =
  target_path := Some path

let full_type_info = ref false

let boolean = ref false

let deadcode = ref false

let init = ref true

let cse = ref false

let tomato = ref false

(* Backward compatibility *)
let set_sigali () = add_target_language "z3z";;

let intermediate = ref false

let nodes_to_inline : string list ref = ref []

let nodes_to_display : string list ref = ref []

let node_to_flatten : string option ref = ref None

let no_mem_alloc = ref false

let use_interf_scheduler = ref false

let use_new_reset_encoding = ref false

let optional f = function
  | None -> None
  | Some x -> Some (f x)

let optunit f = function
  | None -> ()
  | Some x -> f x

(** [split_string s c] splits the string [s] in a list of sub-strings according
    to separator [c]. *)
let rec split_string s c =
  try
    let id = String.index s c in
    let rest = String.sub s (id + 1) (String.length s - id - 1) in
    String.sub s 0 id :: split_string rest c
  with Not_found -> [s]

(* error during the whole process *)
exception Error

(* creation of names. Ensure unicity for the whole compilation chain *)
let symbol = ref 0

let gen_symbol () = incr symbol; "_"^(string_of_int !symbol)
let reset_symbol () = symbol := (*!min_symbol*) 0

open Format
open Unix

let print_header_info ff cbeg cend =
  let tm = Unix.localtime (Unix.time ()) in
  fprintf ff "%s --- Generated the %d/%d/%d at %d:%d --- %s@\n"
    cbeg tm.tm_mday (tm.tm_mon+1) (tm.tm_year + 1900) tm.tm_hour tm.tm_min cend;
  fprintf ff "%s --- heptagon compiler, version %s (compiled %s) --- %s@\n"
    cbeg version date cend;
  fprintf ff "%s --- Command line: %a--- %s@\n@\n"
    cbeg
    (fun ff a ->
       Array.iter (fun arg -> fprintf ff "%s " arg) a)
    Sys.argv
    cend

let unique l =
  let tbl = Hashtbl.create 10 in (* You could replace 10 with List.length l *)
  List.iter (fun i -> Hashtbl.replace tbl i ()) l;
  Hashtbl.fold (fun key data accu -> key :: accu) tbl []

type iterator_name = 
    Imap
  | Ifold
  | Imapfold

let iterator_to_string i = 
  match i with 
    | Imap -> "map"
    | Ifold -> "fold"
    | Imapfold -> "mapfold"

let rec incomplete_map f l =
  match l with 
    | [] -> []
    | [a] -> [a]
    | a::l -> (f a)::(incomplete_map f l)

let rec last_element l =
  match l with 
    | [] -> assert false
    | [v] -> v
    | v::l -> last_element l

(** [split_last l] returns l without its last element and
    the last element of l. *)
let rec split_last = function
  | [] -> assert false
  | [a] -> [], a
  | v::l -> 
      let l, a = split_last l in
	v::l, a

let remove x l =
  List.filter (fun y -> x <> y) l

let is_empty = function
  | [] -> true
  | _ -> false

(** [repeat_list v n] returns a list with n times the value v. *)
let repeat_list v n =
  let rec aux = function
    | 0 -> []
    | n -> v::(aux (n-1))
  in
    aux n

(** Same as List.mem_assoc but using the value instead of the key. *)
let rec memd_assoc value = function
  | [] -> false
  | (k,d)::l -> (d = value) or (memd_assoc value l)

(** Same as List.assoc but searching for a data and returning the key. *)
let rec assocd value = function
  | [] -> raise Not_found
  | (k,d)::l -> 
      if d = value then
	k 
      else
	assocd value l
