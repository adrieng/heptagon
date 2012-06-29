
SIM_PROG=radiotrans
# same as SIM_PROG, capitalized
SIM_MOD=Radiotrans
SIM_NODE=main

# This generic Makefile does not allow contract and simulated node in
# two different modules (can be two different nodes, though)
CONTRACT_PROG=$(SIM_PROG)
CONTRACT_MOD=$(SIM_MOD)
CONTRACT_NODE=main

CC=gcc
HEPTC=heptc -hepts
HEPTS=hepts
SIGALI=sigali

HEPT_LIB_C=/usr/local/lib/heptagon/c

CTRLR_PROG=$(CONTRACT_NODE)_controller

HEPT_PATH=$(shell pwd)

# Path to C headers
HEPT_CINCLUDES=
CFLAGS= $(HEPT_CINCLUDES) -I $(CTRLR_PROG)_c -I $(HEPT_LIB_C)


HEPT_SOURCES = $(wildcard *.ept)
HEPT_MODNAMES = $(patsubst %.ept,%,$(HEPT_SOURCES))

HEPT_C_FILES = $(shell echo $(HEPT_SOURCES) | sed -r 's+([^ ]*).ept+\1_c/\1.c+g')
#HEPT_C_FILES = $(patsubst %.ept,%_c/%.c,$(HEPT_SOURCES))
HEPT_C_DIRS = $(patsubst %.ept,%_c,$(HEPT_SOURCES))
HEPT_Z3Z_DIRS = $(patsubst %.ept,%_z3z,$(HEPT_SOURCES))
HEPT_OBJS = $(HEPT_C_FILES:.c=.o)

CFLAGS += $(patsubst %, -I %,$(HEPT_C_DIRS))


# define NODES_template
# NODES_$(2) = $$(shell grep \\bnode\\b $(1) | sed -r 's/^.*node ([a-zA-Z0-9_]*)[^a-zA-Z0-9_].*$$$$/\1/g')

# Z3Z_FILES_$(2) = $$(patsubst %,$(2)_z3z/%.z3z,$$(NODES_$(2)))
# HEPT_Z3Z_FILES += $$(Z3Z_FILES_$(2))
# HEPT_Z3Z_DIRS += $(2)_z3z
# endef


# $(foreach ept,$(HEPT_SOURCES),$(eval $(call NODES_template,$(ept),$(shell basename $(ept) .ept))))


CTRLR_C_FILES = $(CTRLR_PROG)_c/$(CTRLR_PROG).c
CTRLR_OBJS = $(CTRLR_C_FILES:.c=.o)

all: sim

sim: $(SIM_NODE)_sim $(SIM_PROG).epci
	$(HEPTS) -mod $(SIM_MOD) -node $(SIM_NODE) -exec ./$(SIM_NODE)_sim

$(SIM_NODE)_sim: $(SIM_PROG)_c/_main.o $(HEPT_OBJS) $(CTRLR_OBJS)
	$(CC) $(LDFLAGS) -o $(SIM_NODE)_sim $^

# define HEPT_template
# $(1).epci $$(C_FILES_$(1)) $(1): $(1).ept
# 	hec -target c $(1).ept
# endef

# $(foreach ept,$(HEPT_SOURCES), $(eval $(call HEPT_template,$(shell basename $(ept) .ept))))

$(CONTRACT_PROG)_z3z/$(CONTRACT_NODE).z3z: $(CONTRACT_PROG).ept
	$(HEPTC) -target c -target z3z -s $(SIM_NODE) $(CONTRACT_PROG).ept

$(CONTRACT_PROG).epci \
$(CONTRACT_PROG)_c/$(CONTRACT_PROG).c \
$(CONTRACT_PROG)_c/_main.c: $(CONTRACT_PROG)_z3z/$(CONTRACT_NODE).z3z

# %.epci %_c/%.c: %.ept
# 	$(HEPTC) -target c $<

%.epci: %.epi
	$(HEPTC) $<

$(CTRLR_PROG).ept: $(CONTRACT_PROG)_z3z/$(CONTRACT_NODE).z3z
	$(SIGALI) < $(CONTRACT_PROG)_z3z/$(CONTRACT_NODE).z3z

$(CTRLR_PROG).epci $(CTRLR_PROG)_c/$(CTRLR_PROG).c: $(CTRLR_PROG).ept
	$(HEPTC) -target c $(CTRLR_PROG).ept

%.o: %.c
	$(CC) -c $(CFLAGS) $< -o $@

clean:
	rm -fr $(HEPT_C_DIRS) $(HEPT_Z3Z_DIRS) $(HEPT_JAVA_DIRS)
	rm -f $(SIM_NODE)_sim main.*
	rm -f *.epci *.mls *.ml *.obc ./*~
	rm -f $(CTRLR_PROG).ept

# Dependences

#provadm.epci $(C_FILES_provadm) provadm: provadm_ctrl.epci

$(HEPT_OBJS) $(SIM_PROG)_c/_main.o: $(CTRLR_C_FILES)
