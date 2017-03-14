(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
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

(* $Id: simulator.ml 2418 2011-01-13 20:55:13Z delaval $ *)

(* Graphical simulator *)

open Compiler_utils
open Modules
open Signature
open Names
open Types
open Printf

let print_debug s =
  Printf.printf "%s\n" s;
  flush stdout

let autostep = ref None

let running_thread = ref None
let running_period = ref 0.5

type simtype = Tbool | Tint | Treal | Tother

let simtype_of_type ty =
  match Modules.unalias_type ty with
  | Tid{ qual = Pervasives; name = "int" }   -> Tint
  | Tid{ qual = Pervasives; name = "float" } -> Treal
  | Tid{ qual = Pervasives; name = "bool" }  -> Tbool
  | _ -> Tother


type output_format = Rif | VCD

type chrono_viewer = Sim2chro | GtkWave

class type input =
object
  method get_input : string
  method get_random_input : string
  method set_input : string -> unit
  method reset : unit
end

class boolean_input (table:GPack.table) n : input =
  let value = ref false in
  let click_processed = ref false in
  let but_true = GButton.toggle_button ~label:"true" ~active:false () in
  let _ = table#attach ~expand:`BOTH ~left:1 ~right:2 ~top:n but_true#coerce in
  let but_false = GButton.toggle_button ~label:"false" ~active:true () in
  let _ = table#attach ~expand:`BOTH ~left:2 ~right:3 ~top:n but_false#coerce in
  let toggle new_value =
    value := new_value;
    click_processed := true;
    but_false#set_active (not !value);
    but_true#set_active !value;
    click_processed := false;
  in
  let click button_clicked () =
    if not !click_processed then
      begin
  click_processed := true;
  value := not !value;
  begin match button_clicked with
  | false ->
      but_true#set_active !value
  | true ->
      but_false#set_active (not !value)
  end;
  begin match !autostep with
  | None -> ()
  | Some f -> f ()
  end;
  click_processed := false
      end
  in
  let _ = (but_true#connect#clicked ~callback:(click true)) in
  let _ = (but_false#connect#clicked ~callback:(click false)) in
object
  method get_input =
    if !value then "1" else "0"
  method get_random_input =
    let v = Random.bool () in
    toggle v;
    if v then "1" else "0"
  method set_input s =
    let v = match s with
      | "0" | "f" | "false" -> false
      | _ -> true in
    toggle v
  method reset =
    toggle false
end

class enum_input mod_name value_list (table:GPack.table) n : input =
  let mod_name = modul_to_string mod_name in
  let value = ref ((List.hd value_list).name) in
  let click_processed = ref false in

  let nb_values = List.length value_list in
  let buttons_frame  = GPack.table ~columns:nb_values ~rows:1 () in
  let _ = table#attach
    ~expand:`BOTH ~left:1 ~right:3 ~top:n buttons_frame#coerce in

  let rec create_buttons n first = function
      [] -> []
    | { name = value } :: value_list ->
  let but = GButton.toggle_button ~label:value ~active:first () in
  let _ = buttons_frame#attach
    ~expand:`BOTH ~left:n ~right:(n+1) ~top:0 but#coerce in
  (value,but) :: (create_buttons (n+1) false value_list) in

  let buttons = create_buttons 0 true value_list in
  let array_buttons = Array.of_list buttons in

  let active_button = ref (snd (List.hd buttons)) in

  let _ = List.iter
    (fun (v,b) ->
       let click () =
   if not !click_processed then
     begin
       click_processed := true;
       value := v;
       !active_button#set_active false;
       b#set_active true;
       active_button := b;
       begin match !autostep with
       | None -> ()
       | Some f -> f ()
       end;
       click_processed := false
     end in
       ignore(b#connect#clicked ~callback:click)
    )
    buttons in

object
  method get_input =
    !value
  method get_random_input =
    let i = Random.int (Array.length array_buttons) in
    let (v,b) = array_buttons.(i) in
    click_processed := true;
    value := mod_name ^ "_" ^ v;
    !active_button#set_active false;
    b#set_active true;
    active_button := b;
    click_processed := false;
    !value
  method set_input v =
    let b = List.assoc v buttons in
    click_processed := true;
    value := mod_name ^ "_" ^ v;
    !active_button#set_active false;
    b#set_active true;
    active_button := b;
    click_processed := false
  method reset = ()
end

class entry_input default_value (table:GPack.table) n : input =
  let entry = GEdit.entry ~text:default_value () in
  let _ = table#attach ~expand:`BOTH ~left:1 ~right:3 ~top:n entry#coerce in
object
  method get_input =
    entry#text
  method get_random_input =
    entry#text
  method set_input s =
    entry#set_text s
  method reset = ()
end

class scale_input default_value lower upper to_float from_float digits
  (table:GPack.table) n : input =
  let adj =
    GData.adjustment
      ~value:default_value
      ~lower:lower
      ~upper:upper
      () in
  let scale =
    GRange.scale
      `HORIZONTAL
      ~adjustment:adj
      ~digits:digits
      ~draw_value:true
      () in
  let _ = table#attach ~expand:`BOTH ~left:1 ~right:3 ~top:n scale#coerce in
object
  method get_input =
    from_float adj#value
  method get_random_input =
    begin match (Random.int 4) with
    | 0 -> adj#set_value (max adj#lower (adj#value -. adj#step_increment))
    | 3 -> adj#set_value (min adj#upper (adj#value +. adj#step_increment))
    | _ -> ()
    end;
    from_float adj#value
  method set_input v =
    adj#set_value (to_float v)
  method reset = ()
end


class type output =
object
  method set_output : string -> unit
end

class label_output (table:GPack.table) n : output =
  let label = GMisc.label ~text:"" () in
  let _ = table#attach ~expand:`BOTH ~left:1 ~right:2 ~top:n label#coerce in
object
  method set_output s =
    label#set_text s
end

let sim2chro_type ty =
  match ty with
  | Tint -> "int"
  | Treal -> "real"
  | Tbool -> "int"
  | _ -> "string"

(* input : 1 label, 1 field or two (bool) or more (enum) buttons *)
let create_input v_name v_ty n (table:GPack.table) =
  let label = GMisc.label ~text:v_name () in
  table#attach ~expand:`BOTH ~left:0 ~right:1 ~top:n label#coerce;
  match v_ty with
  | Tid{ qual = Pervasives; name = "int" } ->
      new scale_input
        0. (-60.) 60. float_of_string
        (fun v ->
          string_of_int (int_of_float v))
        0
        table n
  | Tid{ qual = Pervasives; name = "float" } ->
      new scale_input 0. (-100.) 100. float_of_string string_of_float 1 table n
  | Tid{ qual = Pervasives; name = "bool" } ->
      new boolean_input table n
  | Tid(name) ->
     let rec input name =
       let _ = check_type name in
       begin try
           let ty = find_type name in
           begin
             match ty with
             | Tenum(clist) -> new enum_input name.qual clist table n
             | Talias(Tid name) -> input name
             | _ -> new entry_input "" table n
           end
         with Not_found ->
           new entry_input "" table n
       end in
     input name
  | _ -> failwith("Arrays and tuples not yet implemented")

let create_output v_name _v_ty n (table:GPack.table) =
  let label = GMisc.label ~text:v_name () in
  table#attach ~expand:`BOTH ~left:0 ~right:1 ~top:n label#coerce;
  new label_output table n

let find_in_path filename =
  let rec find path =
    match path with
        [] -> raise(Cannot_find_file filename)
      | a::rest ->
          let b = Filename.concat a filename in
            if Sys.file_exists b then b else find rest in
  if Sys.file_exists filename then
    filename
  else if not(Filename.is_implicit filename) then
    raise(Cannot_find_file filename)
  else
    try
      let path = Sys.getenv "PATH" in
      Printf.printf "PATH = %s\n" path;
      let path = Str.split (Str.regexp ":") path in
      find path
    with
        Cannot_find_file _ | Not_found ->
          Printf.printf
            "Warning: command %s not found in your path \
             (set $PATH variable).\n\
             Only a minimal chronogram tool will be provided.\n" filename;
          raise Not_found

let usage_msg = "Usage: " ^
  Sys.executable_name ^ " -mod <Module> -node <node> -exec <exec> [OPTION]...\n" ^
"       " ^  Sys.executable_name ^ " -sig <file>.epci -node <node> -exec <exec> [OPTION]..."
and doc_sig  = "<file>.epci\tCompiled interface containing node <node> (for backward compatibility)"
and doc_mod  = "<Module>\tModule containing node <node>"
and doc_node = "<node>\tName of simulated node"
and doc_exec = "<exec>\tSimulation executable"
and doc_sim2chro = "\tOutput to the sim2chro chronogram viewer tool (by default)"
and doc_gtkwave = "\tOutput to the GtkWave chronogram viewer tool"
and doc_noviewer = "\tNo chronogram viewer used: output to stdout"
and doc_vcd = "\tOutput in VCD (Value Change Dump) format (Rif format by default)"

let main () =

  let nb_step   = ref 0 in
  let saves     = ref [] in

  let mod_name = ref "" in
  let node_name = ref "" in
  let exec_name = ref "" in

  let format = ref Rif in
  let viewer = ref (Some Sim2chro) in

  let mod_name_of_epci epci_name =
    if Filename.check_suffix epci_name ".epci" then
      begin
        let filename = Filename.chop_suffix epci_name ".epci" in
        mod_name := String.capitalize_ascii(Filename.basename filename)
      end
    else
      raise (Arg.Bad("Invalid compiled interface: " ^ epci_name)) in

  let arg_list =
    [
      "-sig",Arg.String mod_name_of_epci,doc_sig; (* Backward compatibility *)
      "-mod",Arg.Set_string mod_name,doc_mod;
      "-node",Arg.Set_string node_name,doc_node;
      "-exec",Arg.Set_string exec_name,doc_exec;
      "-sim2chro",Arg.Unit (fun () -> viewer := (Some Sim2chro); format := Rif),doc_sim2chro;
      "-gtkwave",Arg.Unit (fun () -> viewer := (Some GtkWave); format := VCD),doc_gtkwave;
      "-noviewer",Arg.Unit (fun () -> viewer := None),doc_noviewer;
      "-vcd",Arg.Unit (fun () -> format := VCD),doc_vcd
    ] in
  Arg.parse
    arg_list
    (fun s -> raise (Arg.Bad ("Invalid argument: " ^ s)))
    usage_msg;

  if (!mod_name = "") || (!node_name = "") || (!exec_name = "") then
    begin
      Arg.usage arg_list usage_msg;
      raise Errors.Error
    end;

  open_module (Module !mod_name);

  let signature = find_value { qual = (Module !mod_name);
             name = !node_name } in

  let nb_inputs = List.length signature.node_inputs in
  let nb_outputs = List.length signature.node_outputs in


  ignore (GMain.init ());

  (* main windows *)
  let win      = GWindow.window ~allow_shrink:true ~title:(!node_name ^ " - commands") () in
  let box      = GPack.vbox ~packing:win#add () in
  let up_part  = GPack.paned `VERTICAL ~packing:(box#pack ~expand:true) () in
  let mid_part = GPack.hbox ~packing:(box#pack ~expand:false) () in
  let period_part = GPack.hbox ~packing:(box#pack ~expand:false) () in
  let low_part = GPack.button_box `HORIZONTAL ~packing:(box#pack ~expand:false) () in

  (* Input frame *)
  let in_frame     = GBin.frame ~label:"Inputs" ~packing:up_part#add1 () in
  let scroll_in    =
    GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~packing:in_frame#add () in
  let input_frame  = GPack.table ~columns:3 ~rows:nb_inputs
    ~packing:scroll_in#add_with_viewport () in

  (* Output frame *)
  let out_frame     = GBin.frame ~label:"Outputs" ~packing:up_part#add2 () in
  let scroll_out    =
    GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC ~packing:out_frame#add () in
  (*   let output_frame = GPack.table ~row_spacings:0 ~border_width:1 ~columns:2 ~rows:nb_outputs *)
  (*     ~packing:out_frame#add () in *)
  let output_frame = GPack.table ~columns:2 ~rows:nb_outputs
    ~packing:scroll_out#add_with_viewport () in

  (* Step label *)
  let step_label   = GMisc.label ~text:"Step: -" ~packing:mid_part#add () in
  (* Period scale *)
  let _period_label = GMisc.label ~text:"Period" ~packing:period_part#add () in
  let running_period_adj =
    GData.adjustment
      ~value:!running_period
      ~lower:0.001
      ~upper:1.0
      ~step_incr:0.01
      ~page_incr:0.1
      ~page_size:0.1 () in
  ignore(running_period_adj#connect#value_changed
     ~callback:(fun () -> running_period := running_period_adj#value));
  let _period_scale =
    GRange.scale
      `HORIZONTAL
      ~adjustment:running_period_adj
      ~digits:3
      ~draw_value:true
      ~update_policy:`DISCONTINUOUS
      ~packing:period_part#add
      () in
  (* Step, autostep, random, run, quit buttons *)
  let bstep  = GButton.button ~label:"Step" ~packing:low_part#add () in
  let bastep  =
    GButton.toggle_button ~label:"Autostep" ~packing:low_part#add () in
  let brun  =
    GButton.toggle_button ~label:"Run" ~packing:low_part#add () in
  let brandom =
    GButton.toggle_button ~label:"Random" ~packing:low_part#add () in
  let bquit  = GButton.button ~label:"Quit" ~packing:low_part#add () in

  (* chronogram windows *)
  let chrono = GWindow.window ~title:(!node_name ^ " - chronogram") () in
  let chrono_box = GPack.vbox ~packing:chrono#add () in
  let chrono_chronos =
    GPack.table ~homogeneous:false ~col_spacings:10
      ~columns:11 ~rows:(nb_inputs+nb_outputs)
      ~packing:chrono_box#add () in
  let packing_chrono = chrono_chronos#attach ~expand:`BOTH in
  let chrono_buttons =
    GPack.button_box `HORIZONTAL ~packing:chrono_box#add () in
  let blatex = GButton.button ~label:"Export in LaTeX"
    ~packing:chrono_buttons#add () in
  let btikz = GButton.button ~label:"Export in TikZ"
    ~packing:chrono_buttons#add () in
  let bgnuplot = GButton.button ~label:"Export for Gnuplot"
    ~packing:chrono_buttons#add () in

  let make_label () = GMisc.label ~text:" " () in

  (* create sim2chro process *)
  let oc_simview =
    match !viewer with
      None -> stdout
    | Some Sim2chro ->
      begin
        try
          let file = find_in_path "sim2chro" in
          let oc = Unix.open_process_out (file ^ " -ecran") in
          oc
        with
          Not_found -> stdout
      end
    | Some GtkWave ->
      begin
        try
          let _ = find_in_path "gtkwave" in
          let _ = find_in_path "shmidcat" in
          Unix.open_process_out ("shmidcat | gtkwave -v -I " ^ !node_name ^ ".sav")
        with
          Not_found -> stdout
      end
  in

  (* Print output headers *)

  begin
    match !format with
    | Rif ->
      output_string oc_simview ("#program \"" ^ !node_name ^ "\"\n");
      output_string oc_simview "#@inputs\n"
    | VCD ->
      let tm = Unix.localtime (Unix.time ()) in
      fprintf oc_simview "$date %d/%d/%d %d:%d $end\n"
        tm.Unix.tm_mday (tm.Unix.tm_mon+1) (tm.Unix.tm_year + 1900) tm.Unix.tm_hour tm.Unix.tm_min;
      fprintf oc_simview "$version Heptagon simulator 1.0 $end\n";
      fprintf oc_simview "$timescale 1 ms $end\n";
      fprintf oc_simview "$scope module top $end\n"
  end;

  (* Adding inputs *)

  let inputs,_ =
    List.fold_left
      (fun (acc,n) { a_name = name; a_type = ty } ->
        let name =
          match name with
          | None -> "Input " ^ (string_of_int n)
          | Some name -> name in
        let input = create_input name ty n input_frame in
        let _chrono_label =
          GMisc.label ~text:name ~packing:(packing_chrono ~left:0 ~top:n) () in
        let chrono_data =
          Array.init 10
            (fun i ->
              let lab = make_label () in
              packing_chrono ~left:(i+1) ~top:n lab#coerce;
              lab) in
        let save = ref [] in
        let ty = simtype_of_type ty in
        saves := (name, save)::!saves;
        begin
          match !format with
          | Rif -> fprintf oc_simview "\"%s\":%s\n" name (sim2chro_type ty);
          | VCD ->
            let vartype, size =
              begin match ty with
                Tbool -> "wire", 1
              | Tint -> "integer", 32
              | Treal -> "real", 32
              | Tother -> "event", 1
              end in
            fprintf oc_simview "$var %s %d %s %s $end\n" vartype size name name;
        end;
        ((name,ty,input,chrono_data,save)::acc),(n+1))
      ([],0)
      signature.node_inputs in

  let inputs = List.rev inputs in

  begin match !format with
  | Rif ->
    output_string oc_simview "@#\n";
    output_string oc_simview "#@outputs\n";
  | _ -> ()
  end;

  (* Adding outputs *)

  let outputs,_ =
    List.fold_left
      (fun (acc,n) { a_name = name; a_type = ty } ->
        let name =
          match name with
          | None -> "Output " ^ (string_of_int n)
          | Some name -> name in
        let output = create_output name ty n output_frame in
        let n = n + nb_inputs in
        let _chrono_label =
          GMisc.label ~text:name ~packing:(packing_chrono ~left:0 ~top:n) () in
        let chrono_data =
          Array.init 10
            (fun i ->
              let lab = make_label () in
              packing_chrono ~left:(i+1) ~top:n lab#coerce;
              lab) in
        let save = ref [] in
        let ty = simtype_of_type ty in
        begin
          match !format with
          | Rif -> fprintf oc_simview "\"%s\":%s\n" name (sim2chro_type ty);
          | VCD ->
            let vartype, size =
              begin match ty with
                Tbool -> "wire", 1
              | Tint -> "integer", 32
              | Treal -> "real", 32
              | Tother -> "event", 1
              end in
            fprintf oc_simview "$var %s %d %s %s $end\n" vartype size name name;
        end;
        saves := (name, save)::!saves;
        ((name,ty,output,chrono_data,save)::acc),(n+1))
      ([],0)
      signature.node_outputs in

  let outputs = List.rev outputs in

  let all_vars =
    (List.map (fun (name,ty,_,chrono_data,save) -> (name,ty,chrono_data,save)) inputs) @
    (List.map (fun (name,ty,_,chrono_data,save) -> (name,ty,chrono_data,save)) outputs) in

  (* create simulating process *)
  let (ic_sim,oc_sim) = Unix.open_process !exec_name in

  (* Exports of traces *)

  let open_filedlg outf default_filename () =
    (* File chooser dialog for exports *)
    let dlg = GWindow.file_chooser_dialog ~action:`SAVE () in
    dlg#add_select_button_stock `SAVE `SAVE_EVENT;
    dlg#add_button_stock `CANCEL `CANCEL_EVENT;
    let callback evt =
      match evt with
      | `DELETE_EVENT -> ()
      | `CANCEL_EVENT -> dlg#misc#hide ()
      | `SAVE_EVENT ->
        begin match dlg#filename with
          None -> ()
        | Some f -> outf f
        end;
        dlg#misc#hide ()
    in
    ignore(dlg#connect#response ~callback:callback);
    ignore(dlg#set_filename default_filename);
    dlg#show ()
  in

  let output_latex filename =
    let oc = open_out filename in
    output_string oc "\\[\n";
    output_string oc "\\begin{array}{l|";
    output_string oc (String.make (List.length !((fun (_,_,_,s) -> s) (List.hd all_vars))) 'c');
    output_string oc "c}\n";
    output_string oc "\\hline\n";
    List.iter
      (fun (name,_,_,save) ->
        output_string oc ("\\mbox{\\tt " ^ name ^ "}");
        List.iter
          (fun x -> output_string oc (" & " ^ x))
          (List.rev !save);
        output_string oc " & ...\\\\ ";
        output_string oc "\\hline\n")
      all_vars;
    output_string oc "\\end{array}\n\\]\n";
    close_out oc in

  let output_tikz filename =
    let oc = open_out filename in

    (* printing with grouped repeated values *)
    (* [n] is the number of occurrence of [List.hd s] directly preceding [s] *)
    let print_signal print_value s =
      let rec print n s =
        match s,n with
          [],_ -> ()
        | [x],0 -> print_value oc x
        | [x],_ -> fprintf oc " %d%a" (n+1) print_value x
        | x1 :: ((x2 :: _) as l),_ when x1 = x2 -> print (n+1) l
        | x :: l, 0 -> print_value oc x; print 0 l
        | x :: l, _ -> fprintf oc " %d%a" (n+1) print_value x; print 0 l
      in print 0 s
    in

    output_string oc "\\begin{tikztimingtable}\n";
    List.iter
      (fun (name,ty,_,save) ->
        output_string oc (name ^ " & ");
        print_signal
          (match ty with
            Tbool -> (fun oc x -> output_string oc (if x = "0" then "L" else "H"))
          | _ -> (fun oc x -> output_string oc ("D{" ^ x ^ "}")))
          (List.rev !save);
        output_string oc " \\\\\n")
      all_vars;
    output_string oc "\\end{tikztimingtable}\n";
    close_out oc
  in

  let output_gnuplot () =
    let dt = 1.0 in
    List.iter
      (fun (name,_,_,save) ->
        let oc = open_out (name ^ ".gnuplot") in
        let t = ref 0.0 in
          List.iter
            (fun x ->
              output_string oc ((string_of_float !t) ^ "\t" ^ x ^ "\n");
              t := !t +. dt)
            (List.rev !save);
          close_out oc)
        all_vars
    in

  begin match !format with
  | Rif -> output_string oc_simview "@#\n";
  | VCD ->
    output_string oc_simview "$upscope $end\n";
    output_string oc_simview "$enddefinitions $end\n";
    output_string oc_simview "#1\n"
  end;

  flush oc_simview;

  let step_rif (i,o) =
      output_string oc_simview ("#step " ^ (string_of_int !nb_step) ^ "\n");
      let print_value v =
        output_string oc_simview (v ^ "\t") in
      List.iter print_value (List.rev i);
      output_string oc_simview "#outs\t";
      List.iter print_value (List.rev o);
      output_string oc_simview "\n";
      flush oc_simview
  in

  let step_vcd () =
    List.iter
      (fun (name,ty,_,save) ->
        let print x =
          begin match ty with
          | Tbool -> fprintf oc_simview "%s%s\n" x name (* 1/0 value *)
          | Tint | Treal -> fprintf oc_simview "r%s %s\n" x name (* "real" value *)
          | Tother -> fprintf oc_simview "x %s\n" name (* "x" -> "unknown" value *)
          end in
        match !save with
        | x1 :: x2 :: _ when x1 <> x2 -> print x1
        | [x] -> print x
        | _ -> ()
      )
      all_vars;
    fprintf oc_simview "#%d\n" (!nb_step + 1);
    flush oc_simview
  in

  let step () =
    incr nb_step;
    (* write inputs to simulating process *)
    let input_strings =
      List.fold_left
        (fun acc (_name,_ty,input,chrono,save) ->
          let s =
            if brandom#active
            then input#get_random_input
            else input#get_input in
          input#reset;
          Printf.fprintf oc_sim "%s\n" s;
          save := s::!save;
          if !nb_step <= 10 then
            ignore
              (List.fold_right
                 (fun x i ->
                   (chrono.(i))#set_text x ; i+1)
                 !save 0)
          else
            begin
              (chrono.(0))#set_text "...";
              for i = 1 to 9 do
                (chrono.(i))#set_text (List.nth !save (9-i))
              done
            end;
          s::acc)
        []
        inputs in

    flush oc_sim;

    (* read outputs *)
    let output_strings =
      List.fold_left
        (fun acc (_name,_ty,output,chrono,save) ->
          let s = input_line ic_sim in
          output#set_output s;
          save := s::!save;
          if !nb_step <= 10 then
            ignore
              (List.fold_right
                 (fun x i ->
                   (chrono.(i))#set_text x ; i+1)
                 !save 0)
          else
            begin
              (chrono.(0))#set_text "...";
              for i = 1 to 9 do
                (chrono.(i))#set_text (List.nth !save (9-i))
              done
            end;
          s::acc)
        []
        outputs in

    begin match !format with
    | Rif -> step_rif (input_strings,output_strings)
    | VCD -> step_vcd ()
    end;

    step_label#set_label ("Step: " ^ (string_of_int !nb_step))
  in

  let toggle_autostep () =
    match !autostep with
    | None -> autostep := Some step
    | Some _f -> autostep := None
  in

  let rec run () =
    step();
    Thread.delay(!running_period);
    match !running_thread with
    | None -> Thread.exit()
    | Some _ -> run ()
  in

  let toggle_run () =
    match !running_thread with
    | None ->
  let t = Thread.create run () in
  running_thread := Some t
    | Some _t -> running_thread := None
  in

  let quit() =
    begin try
      ignore(Unix.close_process_out oc_sim);
      ignore(Unix.close_process_out oc_simview)
    with _ -> ()
    end;
    exit 0 in

  ignore (blatex#connect#clicked ~callback:(open_filedlg output_latex (!node_name ^ ".tex")));
  ignore (btikz#connect#clicked ~callback:(open_filedlg output_tikz (!node_name ^ ".tex")));
  ignore (bgnuplot#connect#clicked ~callback:output_gnuplot);
  chrono#show ();
  ignore (bstep#connect#clicked ~callback:step);
  ignore (bastep#connect#clicked ~callback:toggle_autostep);
  ignore (brun#connect#clicked ~callback:toggle_run);
  ignore (bquit#connect#clicked ~callback:quit);
  ignore (win#connect#destroy ~callback:quit);
  win#show ();
  GtkThread.main () ;;

try main () with Errors.Error -> exit 2;;
