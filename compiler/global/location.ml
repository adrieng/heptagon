(* Printing a location in the source program *)
(* inspired from the source of the Caml Light 0.73 compiler *)

open Lexing
open Parsing

(* two important global variables: [input_name] and [input_chan] *)
type location =
    Loc of position  (* Position of the first character *)
         * position  (* Position of the next character following the last one *)


let input_name = ref ""                 (* Input file name. *)

let input_chan = ref stdin              (* The channel opened on the input. *)

let initialize iname ic =
  input_name := iname;
  input_chan := ic


let no_location =  Loc (dummy_pos, dummy_pos)

let error_prompt = ">"


(** Prints [n] times char [c] on [oc]. *)
let prints_n_chars oc n c = for i = 1 to n do output_char oc c done

(** Prints out to [oc] a line designed to be printed under [line] from file [ic]
  underlining from char [first] to char [last] with char [ch].
  [line] is the index of the first char of line. *)
let underline_line ic oc ch line first last =
  let c = ref ' '
  and f = ref first
  and l = ref (last-first) in
  ( try
    seek_in ic line;
    output_string oc error_prompt;
    while c := input_char ic; !c != '\n' do
      if !f > 0 then begin
        f := !f - 1;
        output_char oc (if !c == '\t' then !c else ' ')
      end
      else if !l > 0 then begin
        l := !l - 1;
        output_char oc (if !c == '\t' then !c else ch)
      end
      else ()
    done
  with End_of_file ->
    if !f = 0 && !l > 0 then prints_n_chars oc 5 ch )


let copy_lines nl ic oc prompt =
  for i = 1 to nl do
    output_string oc prompt;
    (try output_string oc (input_line ic)
     with End_of_file -> output_string oc "<EOF>");
    output_char oc '\n'
  done

let copy_chunk p1 p2 ic oc =
  try for i = p1 to p2 - 1 do output_char oc (input_char ic) done
  with End_of_file -> output_string oc "<EOF>"



let skip_lines n ic =
  try for i = 1 to n do
    let _ = input_line ic in ()
    done
  with End_of_file -> ()



let output_location oc (Loc(p1,p2)) =
  let n1 = p1.pos_cnum - p1.pos_bol in (* character number *)
  let n2 = p2.pos_cnum - p2.pos_bol in
  let np1 = p1.pos_cnum in (* character position *)
  let np2 = p2.pos_cnum in
  let l1 = p1.pos_lnum in (* line number *)
  let l2 = p2.pos_lnum in
  let lp1 = p1.pos_bol in (* line position *)
  let lp2 = p2.pos_bol in
  let f1 = p1.pos_fname in (* file name *)
  let f2 = p2.pos_fname in

  if f1 != f2 then (* Strange case *)
    Printf.fprintf oc
    "File \"%s\" line %d, character %d, to file \"%s\" line %d, character %d\n"
      f1 l1 n1 f2 l2 n2

  else begin
    if l2 > l1 then
      Printf.fprintf oc
        "File \"%s\", line %d-%d, characters %d-%d:\n" f1 l1 l2 n1 n2
    else
      Printf.fprintf oc "File \"%s\", line %d, characters %d-%d:\n" f1 l1 n1 n2;
    (* Output source code *)
    try
      let ic = open_in f1 in

      if l1 == l2 then (
        (* Only one line : copy full line and underline *)
        seek_in ic lp1;
        copy_lines 1 ic oc ">";
        underline_line ic oc '^' lp1 n1 n2 )
      else (
        underline_line ic oc '.' lp1 0 n1; (* dots until n1 *)
        seek_in ic np1;
        (* copy the end of the line l1 after the dots *)
        copy_lines 1 ic oc "";
        if l2 - l1 <= 8 then
          (* copy the 6 or less middle lines *)
          copy_lines (l2-l1-1) ic oc ">"
        else (
          (* sum up the middle lines to 6 *)
          copy_lines 3 ic oc ">";
          output_string oc "..........\n";
          skip_lines (l2-l1-7) ic; (* skip middle lines *)
          copy_lines 3 ic oc ">"
        );
        output_string oc ">";
        copy_chunk lp2 np2 ic oc; (* copy interesting begining of l2 *)
      )
    with Sys_error _ -> ();
    output_char oc '\n'
  end;

