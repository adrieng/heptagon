open Names
open Modules

let rec modul_of_string_list = function
  | [] -> Idents.local_qn
  | ["Pervasives"] -> pervasives_qn
  | [q] -> fun n -> { qual = Module q; name = n}
  | q::q_l ->
      fun n -> { qual = QualModule (modul_of_string_list q_l q); name = n }

let qualname_of_string s =
  let q_l_n = Misc.split_string s "." in
  match List.rev q_l_n with
    | [] -> Misc.internal_error "Names"
    | n::q_l -> modul_of_string_list q_l n

let modul_of_string s =
  let q_l = Misc.split_string s "." in
  let q = modul_of_string_list (List.rev q_l) "" in
  q.qual

