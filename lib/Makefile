include ../config

STDLIB_INTERFACE=pervasives.epi
STDLIB_OBJ=$(STDLIB_INTERFACE:.epi=.epci)

C_DIR=c
C_OBJ=pervasives.h

.SUFFIXES: .epi .epci

.epi.epci:
	../compiler/$(COMPILER).$(TARGET) -nopervasives $<

.PHONY: all install clean

all: $(STDLIB_OBJ)

install: all
	$(INSTALL) -d $(INSTALL_LIBDIR)
	$(INSTALL) $(STDLIB_OBJ) $(STDLIB_INTERFACE) $(INSTALL_LIBDIR)
	$(INSTALL) -d $(INSTALL_LIBDIR)/$(C_DIR)
	(cd c/; $(INSTALL) $(C_OBJ) $(INSTALL_LIBDIR)/$(C_DIR))

clean:
	rm *.epci