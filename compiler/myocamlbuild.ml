open Ocamlbuild_plugin
open Ocamlbuild_plugin.Options

let df = function
  | After_rules ->
      (* Tell ocamlbuild about the camlp4 library. *)
      ocaml_lib ~extern:true ~dir:"+camlp4" "camlp4";

      (* Tell ocamlbuild about Menhir library (needed by --table). *)
      ocaml_lib ~extern:true ~dir:"+menhirLib" "menhirLib";

      (* Tell ocamlbuild about the ocamlgraph library. *)
      ocaml_lib ~extern:true ~dir:"+ocamlgraph" "ocamlgraph";

      (* Menhir does not come with menhirLib.cmxa so we have to manually by-pass
         OCamlbuild's built-in logic and add the needed menhirLib.cmxa. *)
      flag ["link"; "native"; "link_menhirLib"] (S [A "-I"; A "+menhirLib";
                                                    A "menhirLib.cmx"]);
      flag ["link"; "byte"; "link_menhirLib"] (S [A "-I"; A "+menhirLib";
                                                  A "menhirLib.cmo"]);



      (* Add preproc.cmo to the ocaml pre-processor when use_preproc is set *)
      flag ["ocaml"; "pp"; "use_preproc"] (A "preproc.cmo");

      (* Running ocamldep on ocaml code that is tagged with use_preproc will
         require the cmo.  Note that you only need this declaration when the
         syntax extension is part of the sources to be compiled with
         ocamlbuild. *)
      dep ["ocaml"; "ocamldep"; "use_preproc"] ["preproc.cmo"];

      (* LablGTK use for graphical simulator *)
      ocaml_lib ~extern:true ~dir:"+lablgtk2" "lablgtk";
      ocaml_lib ~extern:true "lablgtkthread";

      flag ["ocaml"; "parser" ; "menhir" ; "use_menhir"] (S[A"--explain";
                                                            A"--table"]);

      flag ["ocaml"; "compile" ] (S[A"-w"; A"Ae"; A"-warn-error"; A"PU"; A"-w"; A"-9"]);

  | _ -> ()

let _ = dispatch df
