To build the graphical simulator with ocamlbuild, one has to create an ocaml library
containing gtkThread.cmo (resp. .cmx): it is not in the lablgtk library.

To do so, go to the lablgtk library directory and type:

ocamlc -a gtkThread.cmo -o lablgtkthread.cma
ocamlopt -a gtkThread.cmx -o lablgtkthread.cmxa
