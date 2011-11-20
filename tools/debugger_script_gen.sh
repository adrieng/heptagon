#!/bin/bash
OCAML_LIB=`ocamlc -where`
DIR=`pwd`
echo "load_printer \"${OCAML_LIB}/ocamlgraph/graph.cmo\"
load_printer \"${OCAML_LIB}/menhirLib/menhirLib.cmo\"
load_printer \"${OCAML_LIB}/str.cma\"" > debugger_script
pushd ../compiler > /dev/null
ocamlbuild -clean
ocamlbuild heptc.d.byte | sed -n 's/.*\-o \([^ ]\+.cm[io]\).*/load_printer "_build\/\1"/p' | sed 's/\.cmi/.cmo/' >> $DIR/debugger_script
