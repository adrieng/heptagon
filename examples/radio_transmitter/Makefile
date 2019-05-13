
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
REAX=reax -a sB -s
CTRL2EPT=ctrl2ept

HEPT_LIB_C=/usr/local/lib/heptagon/c

CTRLR_PROG=$(CONTRACT_PROG)_controller

HEPT_PATH=$(shell pwd)

# Path to C headers
HEPT_CINCLUDES=
CFLAGS= $(HEPT_CINCLUDES) -I $(CTRLR_PROG)_c -I $(HEPT_LIB_C)


HEPT_SOURCES = $(wildcard *.ept)
HEPT_MODNAMES = $(patsubst %.ept,%,$(HEPT_SOURCES))

HEPT_C_FILES = $(shell echo $(HEPT_SOURCES) | sed -r 's+([^ ]*).ept+\1_c/\1.c+g')
#HEPT_C_FILES = $(patsubst %.ept,%_c/%.c,$(HEPT_SOURCES))
HEPT_C_DIRS = $(patsubst %.ept,%_c,$(HEPT_SOURCES))
HEPT_CTRLN_DIRS = $(patsubst %.ept,%_ctrln,$(HEPT_SOURCES))
HEPT_OBJS = $(HEPT_C_FILES:.c=.o)

CFLAGS += $(patsubst %, -I %,$(HEPT_C_DIRS))


CTRLR_C_FILES = $(CTRLR_PROG)_c/$(CTRLR_PROG).c
CTRLR_OBJS = $(CTRLR_C_FILES:.c=.o)

all: sim

sim: $(SIM_NODE)_sim $(SIM_PROG).epci
	$(HEPTS) -mod $(SIM_MOD) -node $(SIM_NODE) -exec ./$(SIM_NODE)_sim

$(SIM_NODE)_sim: $(SIM_PROG)_c/_main.o $(HEPT_OBJS) $(CTRLR_OBJS)
	$(CC) $(LDFLAGS) -o $(SIM_NODE)_sim $^

$(CONTRACT_PROG)_ctrln/$(CONTRACT_NODE).ctrln: $(CONTRACT_PROG).ept
	$(HEPTC) -target c -target ctrln -s $(SIM_NODE) $(CONTRACT_PROG).ept

$(CONTRACT_PROG).epci \
$(CONTRACT_PROG)_c/$(CONTRACT_PROG).c \
$(CONTRACT_PROG)_c/_main.c: $(CONTRACT_PROG)_ctrln/$(CONTRACT_NODE).ctrln

# %.epci %_c/%.c: %.ept
# 	$(HEPTC) -target c $<

%.epci: %.epi
	$(HEPTC) $<

$(CTRLR_PROG).ept: $(CONTRACT_PROG)_ctrln/$(CONTRACT_NODE).ctrln
	$(REAX) $(CONTRACT_PROG)_ctrln/$(CONTRACT_NODE).ctrln
	$(CTRL2EPT) -v -m $(CONTRACT_MOD)

$(CTRLR_PROG).epci $(CTRLR_PROG)_c/$(CTRLR_PROG).c: $(CTRLR_PROG).ept
	$(HEPTC) -target c $(CTRLR_PROG).ept

%.o: %.c
	$(CC) -c $(CFLAGS) $< -o $@

clean:
	rm -fr $(HEPT_C_DIRS) $(HEPT_CTRLN_DIRS) $(HEPT_JAVA_DIRS)
	rm -f $(SIM_NODE)_sim main.*
	rm -f *.epci *.mls *.ml *.obc ./*~
	rm -f $(CTRLR_PROG).ept

# Dependences

#provadm.epci $(C_FILES_provadm) provadm: provadm_ctrl.epci

$(HEPT_OBJS) $(SIM_PROG)_c/_main.o: $(CTRLR_C_FILES)
