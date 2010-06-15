# $Id$

DATE = \`eval date\`
LIBDIR = \`eval pwd\`/../lib
BIN = hec
TARGET = opt

OCAMLFLAGS = -dtypes -g
OCAMLOPTFLAGS = -dtypes -g
CPP  = cpp
#gcc -E
CPPFLAGS = -P
SED=sed

# lablgtk
LABLGTKPREFIX = /usr/lib/ocaml
LABLGTKFLAGS = -I $(LABLGTKPREFIX)/lablgtk2 -I $(LABLGTKPREFIX)/stublibs
LABLGTKLINKFLAGS = -dllpath $(LABLGTKPREFIX)/stublibs

OCAMLC = ocamlc
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc
OCAMLOPT = ocamlopt
OCAMLDEP = ocamldep

UNIX = str.cma unix.cma
UNIXX = str.cmxa unix.cmxa
INCLUDES =

DIRECTORIES = global parsing analysis translation dataflow sigali sequential  \
	simulation main

INCLUDES = $(DIRECTORIES:%=-I %)

GENSOURCES = parsing/lexer.ml parsing/parser.mli parsing/parser.ml

GLOBAL = global/names.cmo \
	global/ident.cmo \
	global/static.cmo \
	global/location.cmo \
	global/misc.cmo \
	global/linearity.cmo \
	global/graph.cmo \
	global/dep.cmo \
	global/parsetree.cmo \
	global/heptagon.cmo \
	global/global.cmo \
	global/modules.cmo \
	global/printer.cmo \
	global/initial.cmo \
	global/interference_graph.cmo \
	global/scoping.cmo 
PARSING = parsing/lexer.cmo \
	parsing/parser.cmo
ANALYSIS = analysis/typing.cmo \
	analysis/causal.cmo \
	analysis/causality.cmo \
	analysis/interface.cmo \
	analysis/initialization.cmo \
	analysis/linear_typing.cmo \
	analysis/automata_mem.cmo
TRANSLATION = translation/completion.cmo \
	translation/automata.cmo \
	translation/present.cmo \
	translation/last.cmo  \
	translation/reset.cmo \
	translation/reset_new.cmo \
	translation/every.cmo 
#	translation/inline.cmo
DATAFLOW = dataflow/minils.cmo \
	dataflow/merge.cmo \
	dataflow/dfcausality.cmo \
	dataflow/normalize.cmo \
	dataflow/schedule.cmo \
	dataflow/clocking.cmo \
	dataflow/intermediate.cmo \
	dataflow/cse.cmo \
	dataflow/cmse.cmo \
	dataflow/tomato.cmo \
	dataflow/tommls.cmo \
	dataflow/deadcode.cmo \
	dataflow/mls2dot.cmo \
	dataflow/interference2dot.cmo \
	dataflow/interference.cmo \
	dataflow/memalloc.cmo \
	dataflow/splitting.cmo \
	dataflow/schedule_interf.cmo \
	dataflow/callgraph.cmo
#	dataflow/init.cmo
SIGALI = sigali/boolean.cmo \
	sigali/sigali.cmo \
	sigali/dynamic_system.cmo
SEQUENTIAL = sequential/obc.cmo \
	sequential/control.cmo \
	sequential/translate.cmo \
	sequential/c_old.cmo \
	sequential/caml.cmo \
	sequential/java.cmo \
	sequential/c.cmo \
	sequential/csubst.cmo \
	sequential/rename.cmo \
	sequential/cgen.cmo \
	sequential/vhdl.cmo \
	sequential/mls2vhdl.cmo 
#       sequential/lustre.cmo
MAIN = main/compiler.cmo \
	main/main.cmo

OBJ = $(GLOBAL) $(MODULES) $(PARSING) $(ANALYSIS) $(TRANSLATION) \
			$(DATAFLOW) $(SEQUENTIAL) $(MAIN) \
	$(SIMULATION)

OBJ_OPT = $(OBJ:.cmo=.cmx)

SRC = $(OBJ:.cmo=.ml)

INTERFACES = $(SRC:.ml=.mli)

SIM_BIN = hes

# Objs needed for compiling simulator
SIM_OBJ = global/misc.cmo \
	global/heptagon.cmo \
	global/global.cmo \
	global/modules.cmo \
	simulation/simulator.cmo
SIM_LIBS = lablgtk.cma unix.cma

SIM_OBJ_OPT = $(SIM_OBJ:.cmo=.cmx)

SIM_LIBS_OPT = $(SIM_LIBS:.cma=.cmxa)

world: all

all: $(TARGET)

opt: $(BIN).opt
byte: $(BIN).byte

$(BIN).opt: $(OBJ_OPT)
	$(OCAMLOPT) $(UNIXX) $(OCAMLOPTFLAGS) $(INCLUDES) $(OBJ_OPT) -o $(BIN).opt

$(BIN).byte: $(OBJ)
	$(OCAMLC) -custom $(UNIX) $(OCAMLFLAGS) $(INCLUDES) $(OBJ) -o $(BIN).byte

sim: $(SIM_BIN).byte
simopt:$(SIM_BIN).opt

$(SIM_BIN).opt: $(SIM_OBJ_OPT)
	$(OCAMLOPT) $(OCAMLOPTFLAGS) \
		$(LABLGTKFLAGS) \
		$(INCLUDES) $(SIM_LIBS_OPT) $(SIM_OBJ_OPT) -o $(SIM_BIN).opt
$(SIM_BIN).byte: $(SIM_OBJ)
	$(OCAMLC) -custom $(UNIX) $(OCAMLFLAGS) \
		$(LABLGTKFLAGS) $(LABLGTKLINKFLAGS) \
		$(INCLUDES) $(SIM_LIBS) $(SIM_OBJ) -o $(SIM_BIN).byte


debug: OCAMLFLAGS += -g
debug: byte

profile: OCAMLOPTFLAGS += -p
profile: opt

depend .depend: $(GENSOURCES)
	(for d in $(DIRECTORIES); \
		do $(OCAMLDEP) $(INCLUDES) $$d/*.mli $$d/*.ml; \
		done) > .depend

interfaces: $(INTERFACES)

# Extra dependences
parsing/parser.mli parsing/parser.ml: parsing/parser.mly
	$(OCAMLYACC) -v parsing/parser.mly

parsing/lexer.cmi: parsing/parser.mli

parsing/lexer.ml: parsing/lexer.mll
	$(OCAMLLEX) parsing/lexer.mll

global/misc.cmo: OCAMLFLAGS := \
	-pp "$(SED) -e \"s|DATE|`date`|\" -e \"s|STDLIB|$(LIBDIR)|\""
# -pp "$(CPP) $(CPPFLAGS) -DSTDLIB=\\\"$(LIBDIR)\\\" \
# -DDATE=\\\"\"`date`\"\\\""

global/misc.cmx: OCAMLOPTFLAGS := \
	-pp "$(SED) -e \"s|DATE|`date`|\" -e \"s|STDLIB|$(LIBDIR)|\""
#	-pp "$(CPP) $(CPPFLAGS) -DSTDLIB=\\\"$(LIBDIR)\\\" \
#	-DDATE=\\\"\"`date`\"\\\""

simulation/simulator.cmo: OCAMLFLAGS += $(LABLGTKFLAGS)

simulation/simulator.cmx: OCAMLOPTFLAGS += $(LABLGTKFLAGS)

# Common rules
.SUFFIXES : .mli .ml .cmi .cmo .cmx

%.cmo: %.ml
	$(OCAMLC) $(OCAMLFLAGS) -c $(INCLUDES) $<

%.cmi: %.mli
	$(OCAMLC) $(OCAMLFLAGS) -c $(INCLUDES) $<

%.cmx: %.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $(INCLUDES) $<

# %.mli: %.ml
# 	$(OCAMLC) $(OCAMLFLAGS) -i -c $(INCLUDES) $< > $@



# Clean up
clean:
	rm -f $(GENSOURCES) parsing/parser.output
        # to avoid the make warnings:
	rm -f parsing/parser.ml
	rm -f parsing/lexer.ml
	(for d in $(DIRECTORIES); \
		do rm -f $$d/*.annot $$d/*.cm[iox] $$d/*.o; \
		done)
	rm -f $(BIN).byte $(BIN).opt

ML = $(OBJ:.cmo=.ml)

wc:
	wc $(ML)

include .depend
