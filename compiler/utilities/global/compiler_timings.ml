(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Unix

let current_module = ref ""
let timings = ref []
let compilation_start = ref 0.
let compilation_stop = ref 0.

let start_compiling modname =
  current_module := modname;
  compilation_start := Unix.gettimeofday ()

let elapsed_seconds_between start stop = stop -. start

let time_pass name f x =
  let start = Unix.gettimeofday () in
  let r = f x in
  let stop = Unix.gettimeofday () in
  timings := (name, elapsed_seconds_between start stop) :: !timings;
  r

let report_statistics () =
  if not !Compiler_options.time_passes then ()
  else
    (
      compilation_stop := Unix.gettimeofday ();
      let total_time =
        elapsed_seconds_between !compilation_start !compilation_stop in

      let compute_percent time = int_of_float (time /. total_time *. 100.) in

      let max_size =
        let sizes = List.map (fun (name, _) -> String.length name) !timings in
        List.fold_left max 0 sizes
      in

      let big_space = String.make 4 ' ' in

      let format time =
        let secs = int_of_float time in
        let mins = int_of_float (time /. 60.) in

        let post_secs = if secs > 1 then "s" else " " in
        let post_mins = if mins > 1 then "s" else " " in

        Printf.sprintf "%.2d min%s %.2d sec%s%s" mins post_mins secs post_secs big_space
      in

      let display (name, time) =
        print_string name;
        for i = 1 to max_size - String.length name do
          print_string " "
        done;

        Printf.printf "  %s(%.2d%%)\n" (format time) (compute_percent time)
      in

      let print_sep () =
        for i = 1 to max_size + 22 + String.length big_space do
          print_string "#"
        done;
        Printf.printf "\n"
      in

      print_sep ();

      Printf.printf "Compilation statistics for %s\n" !current_module;

      print_sep ();

      List.iter display (List.rev !timings);

      print_sep ();

      Printf.printf "TOTAL";
      for i = 1 to max_size - 5 do
        print_string " "
      done;
      let percent = List.fold_left (+) 0 (List.map compute_percent (List.map snd !timings)) in
      Printf.printf "  %s(%.2d%%)\n" (format total_time) percent;
      current_module := ""
    )
