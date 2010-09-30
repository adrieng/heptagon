(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* useful stuff *)

let optional f = function
  | None -> None
  | Some x -> Some (f x)

let optional_wacc f acc = function
  | None -> None, acc
  | Some x -> let x, acc = f acc x in Some x, acc

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


(* creation of names. Ensure unicity for the whole compilation chain *)
let symbol = ref 0

let gen_symbol () = incr symbol; "_"^(string_of_int !symbol)
let reset_symbol () = symbol := (*!min_symbol*) 0

let unique l =
  let tbl = Hashtbl.create (List.length l) in
  List.iter (fun i -> Hashtbl.replace tbl i ()) l;
  Hashtbl.fold (fun key _ accu -> key :: accu) tbl []

let rec incomplete_map f l =
  match l with
    | [] -> []
    | [a] -> [a]
    | a::l -> (f a)::(incomplete_map f l)

let rec last_element l =
  match l with
    | [] -> assert false
    | [v] -> v
    | _::l -> last_element l

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

let list_compare c l1 l2 =
  let rec aux l1 l2 = match (l1, l2) with
    | (h1::t1, h2::t2) ->
        let result = c h1 h2 in
        if result = 0 then aux t1 t2 else result
    | ([],     []    ) -> 0
    | (_,      []    ) -> 1
    | ([],     _     ) -> -1
  in aux l1 l2

let option_compare f ox1 ox2 = match ox1, ox2 with
  | None, None -> 0
  | Some x1, Some x2 -> f x1 x2
  | None, _ -> -1
  | _, None -> 1

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
  | (_,d)::l -> (d = value) or (memd_assoc value l)

(** Same as List.assoc but searching for a data and returning the key. *)
let rec assocd value = function
  | [] -> raise Not_found
  | (k,d)::l ->
      if d = value then
        k
      else
        assocd value l


(** { 3 Compiler iterators } *)

(** Mapfold *)
let mapfold f acc l =
  let l,acc = List.fold_left
                (fun (l,acc) e -> let e,acc = f acc e in e::l, acc)
                ([],acc) l in
  List.rev l, acc

let mapfold_right f l acc =
  List.fold_right (fun e (acc, l) -> let acc, e = f e acc in (acc, e :: l))
    l (acc, [])

let mapi f l =
  let rec aux i = function
    | [] -> []
    | v::l -> (f i v)::(aux (i+1) l)
  in
    aux 0 l

let mapi2 f l1 l2 =
  let rec aux i l1 l2 =
    match l1, l2 with
      | [], [] -> []
      | [], _ -> invalid_arg ""
      | _, [] -> invalid_arg ""
      | v1::l1, v2::l2 -> (f i v1 v2)::(aux (i+1) l1 l2)
  in
    aux 0 l1 l2

let mapi3 f l1 l2 l3 =
  let rec aux i l1 l2 l3 =
    match l1, l2, l3 with
      | [], [], [] -> []
      | [], _, _ -> invalid_arg ""
      | _, [], _ -> invalid_arg ""
      | _, _, [] -> invalid_arg ""
      | v1::l1, v2::l2, v3::l3 ->
          (f i v1 v2 v3)::(aux (i+1) l1 l2 l3)
  in
    aux 0 l1 l2 l3

let fold_righti f l acc =
  let rec aux i l acc = match l with
    | [] -> acc
    | h :: l -> f i h (aux (i + 1) l acc) in
  aux 0 l acc

(* Functions to decompose a list into a tuple *)
let _arity_error i l =
  Format.eprintf "Internal compiler error: \
     wrong list size (found %d, expected %d).@." (List.length l) i;
  assert false

let _arity_min_error i l =
  Format.eprintf "Internal compiler error: \
     wrong list size (found %d, expected %d at least).@." (List.length l) i;
  assert false

let assert_empty = function
  | [] -> ()
  | l -> _arity_error 0 l

let assert_1 = function
  | [v] -> v
  | l -> _arity_error 1 l

let assert_1min = function
  | v::l -> v, l
  | l -> _arity_min_error 1 l

let assert_2 = function
  | [v1; v2] -> v1, v2
  | l -> _arity_error 2 l

let assert_2min = function
  | v1::v2::l -> v1, v2, l
  | l -> _arity_min_error 2 l

let assert_3 = function
  | [v1; v2; v3] -> v1, v2, v3
  | l -> _arity_error 3 l
