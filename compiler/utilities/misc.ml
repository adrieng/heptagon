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


(** Print to a string *)
let print_pp_to_string print_fun element =
  let _ = Format.flush_str_formatter () in (* Ensure that the buffer is empty *)
  print_fun Format.str_formatter element;
  Format.flush_str_formatter ()

(** Replace all non [a-z A-Z 0-9] character of a string by [_] *)
let sanitize_string s =
  Str.global_replace (Str.regexp "[^a-zA-Z0-9]") "_" s


(* creation of names. Ensure unicity for the whole compilation chain *)
let symbol = ref 0

let gen_symbol () = incr symbol; "_"^(string_of_int !symbol)
let reset_symbol () = symbol := (*!min_symbol*) 0

let unique l =
  let tbl = Hashtbl.create (List.length l) in
  List.iter (fun i -> Hashtbl.replace tbl i ()) l;
  Hashtbl.fold (fun key _ accu -> key :: accu) tbl []

let rec map_butlast f l =
  match l with
    | [] -> []
    | [a] -> [a]
    | a::l -> (f a)::(map_butlast f l)

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

exception List_too_short
(** [split_at n l] splits [l] in two after the [n]th value.
    Raises List_too_short exception if the list is too short. *)
let rec split_at n l = match n, l with
  | 0, l -> [], l
  | _, [] -> raise List_too_short
  | n, x::l ->
      let l1, l2 = split_at (n-1) l in
        x::l1, l2

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

(** Mapfold *) (* TODO optim : in a lot of places we don't need the List.rev *)
let mapfold f acc l =
  let l,acc = List.fold_left
                (fun (l,acc) e -> let e,acc = f acc e in e::l, acc)
                ([],acc) l in
  List.rev l, acc

let mapfold2 f acc l1 l2 =
  let l,acc = List.fold_left2
                (fun (l,acc) e1 e2 -> let e,acc = f acc e1 e2 in e::l, acc)
                ([],acc) l1 l2 in
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

exception Assert_false
let internal_error passe code =
  Format.eprintf "@.---------\n
                  Internal compiler error\n
                  Passe : %s, Code : %d\n
                  ----------@." passe code;
  raise Assert_false

exception Unsupported
let unsupported passe code =
  Format.eprintf "@.---------\n
                  Unsupported feature, please report it\n
                  Passe : %s, Code : %d\n
                  ----------@." passe code;
  raise Unsupported

(* Functions to decompose a list into a tuple *)
let _arity_error i l =
  Format.eprintf "@.---------\n
                  Internal compiler error: wrong list size (found %d, expected %d).\n
                  ----------@." (List.length l) i;
  raise Assert_false

let _arity_min_error i l =
  Format.eprintf "@.---------\n
                  Internal compiler error: wrong list size (found %d, expected %d at least).\n
                  ----------@." (List.length l) i;
  raise Assert_false

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

let (|>) x f = f x

let split_string s separator = Str.split (separator |> Str.quote |> Str.regexp) s

let file_extension s = split_string s "." |> last_element

(** Memoize the result of the function [f]*)
let memoize f =
  let map = Hashtbl.create 100 in
    fun x ->
      try
        Hashtbl.find map x
      with
        | Not_found -> let r = f x in Hashtbl.add map x r; r

(** Memoize the result of the function [f], taht should expect a
   tuple as input and be reflexive (f (x,y) = f (y,x)) *)
let memoize_couple f =
  let map = Hashtbl.create 100 in
    fun (x,y) ->
      try
        Hashtbl.find map (x,y)
      with
        | Not_found ->
            let r = f (x,y) in Hashtbl.add map (x,y) r; Hashtbl.add map (y,x) r; r

(** [iter_couple f l] calls f for all x and y distinct in [l].  *)
let rec iter_couple f l = match l with
  | [] -> ()
  | x::l ->
      List.iter (f x) l;
      iter_couple f l

(** [iter_couple_2 f l1 l2] calls f for all x in [l1] and y in [l2].  *)
let iter_couple_2 f l1 l2 =
  List.iter (fun v1 -> List.iter (f v1) l2) l1

(** [index p l] returns the idx of the first element in l
    that satisfies predicate p.*)
let index p l =
  let rec aux i = function
    | [] -> -1
    | v::l -> if p v then i else aux (i+1) l
  in
    aux 0 l
