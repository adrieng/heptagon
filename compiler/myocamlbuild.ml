open Ocamlbuild_plugin
open Ocamlbuild_plugin.Options
open Myocamlbuild_config

let df = function
  | Before_options ->  ocamlfind_before_options ()
  | After_rules ->
      ocamlfind_after_rules ();

      (* Tell ocamlbuild about the camlp4 library. *)
      ocaml_lib ~extern:true ~dir:(ocamlfind_query "camlp4") "camlp4";

      (* Add preproc.cmo to the ocaml pre-processor when use_preproc is set *)
      flag ["ocaml"; "pp"; "use_preproc"] (A "preproc.cmo");

      (* Running ocamldep on ocaml code that is tagged with use_preproc will
         require the cmo.  Note that you only need this declaration when the
         syntax extension is part of the sources to be compiled with
         ocamlbuild. *)
      dep ["ocaml"; "ocamldep"; "use_preproc"] ["preproc.cmo"];

      flag ["ocaml"; "parser" ; "menhir" ; "use_menhir"] (S[A"--explain";
                                                            A"--table"]);

      flag ["ocaml"; "compile" ] (S[A"-w"; A"Ae"; A"-warn-error"; A"PU"; A"-w"; A"-9"]);

  | _ -> ()

let _ = dispatch df
