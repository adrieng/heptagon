#!/bin/bash
OCAML_LIB=`ocamlc -where`
echo "load_printer \"${OCAML_LIB}/ocamlgraph/graph.cmo\"
load_printer \"${OCAML_LIB}/menhirLib/menhirLib.cmo\"
load_printer \"${OCAML_LIB}/str.cma\"" > debugger_script
ocamlbuild -clean
ocamlbuild heptc.d.byte | sed -n 's/.*\-o \([^ ]\+.cm[io]\).*/load_printer "_build\/\1"/p' | sed 's/\.cmi/.cmo/' >> debugger_script
