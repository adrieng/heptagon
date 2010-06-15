open Ocamlbuild_plugin
open Ocamlbuild_plugin.Options

let sub_dirs = ["global"; "parsing"; "sigali"; "dataflow"; "sequential";
                "analysis"; "translation"; "main"; "simulation"]

let df = function
  | Before_options ->
      include_dirs := sub_dirs @ !include_dirs
  | After_rules ->
      (* Tell ocamlbuild about the camlp4 library. *)
      ocaml_lib ~extern:true ~dir:"+camlp4" "camlp4";

      (* Add preproc.cmo to the ocaml pre-processor when use_preproc is set *)
      flag ["ocaml"; "pp"; "use_preproc"] (A "preproc.cmo");
      (* Running ocamldep on ocaml code that is tagged with use_preproc will
         require the cmo.  Note that you only need this declaration when the
         syntax extension is part of the sources to be compiled with
         ocamlbuild. *)
      dep ["ocaml"; "ocamldep"; "use_preproc"] ["preproc.cmo"];

      (* LablGTK use for graphical simulator *)
      ocaml_lib ~extern:true ~dir:"+lablgtk2" "lablgtk"
  | _ -> ()

let _ = dispatch df
