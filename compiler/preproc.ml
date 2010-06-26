(** {1 Micro pre-processor for Heptagon}

    This module uses camlp4 to replace some fixed strings by string literals at
    compile-time. At the moment, we only replace DATE by the current date and
    STDLIB by "../../lib". Each pseudo-variable can be overriden by the
    environment variable of the same name. *)

open Camlp4.PreCast
open Unix

(** {2 Compile-time strings} *)

(** [date] is a string denoting the current date. *)
let date =
  let days = [| "sunday"; "monday"; "tuesday"; "wednesday"; "thursday";
                "friday"; "saturday" |]
  and months = [| "january"; "february"; "march"; "april"; "may"; "june";
                  "july"; "august"; "september"; "october"; "november";
                  "december" |] in

  let tm = Unix.localtime (Unix.gettimeofday ()) in

  let (day, month) =
    let prefix s = String.sub s 0 3 in
    (prefix days.(tm.tm_wday), prefix months.(tm.tm_mon)) in

  Printf.sprintf "%s. %s. %d %d:%d:%d CET %d"
    day month tm.tm_mday tm.tm_hour tm.tm_min tm.tm_sec (1900 + tm.tm_year)


(** [stdlib] is the location of the standard Heptagon library. *)
let stdlib =
  let wd = Unix.getcwd () in
  Filename.concat (Filename.dirname (Filename.dirname wd)) "lib"

(** Association list defining bindings between constant and our "compile-time
    constants". *)
let env = [("DATE", date); ("STDLIB", stdlib)]

(** {2 Camlp4 hook} *)

(** Our home-grown super-duper syntax filter. Looks for string constants present
    in [subst] and replaces them according to the couple found in the
    environment defined above. *)
let filter =
object
  inherit Ast.map as super
  method expr e = match e with
    | <:expr< $str:s$ >> when List.mem_assoc s env ->
      let repl = try Sys.getenv s with Not_found -> List.assoc s env in
      <:expr@here< $str:repl$ >>
    | x -> x
end;;

(** Tell Camlp4 about it. *)
AstFilters.register_str_item_filter filter#str_item
