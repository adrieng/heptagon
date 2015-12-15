include ../config

STDLIB_INTERFACE=pervasives.epi iostream.epi math.epi
STDLIB_OBJ=$(STDLIB_INTERFACE:.epi=.epci)

C_DIR=c
C_OBJ=pervasives.h math.h math.c

.SUFFIXES: .epi .epci

.PHONY: all install clean

all: $(STDLIB_OBJ)

pervasives.epci: pervasives.epi
	../compiler/$(COMPILER).$(TARGET) -nopervasives $<

%.epci: %.epi
	../compiler/$(COMPILER).$(TARGET) $<

install: all
	$(INSTALL) -d $(INSTALL_LIBDIR)
	$(INSTALL) $(STDLIB_OBJ) $(STDLIB_INTERFACE) $(INSTALL_LIBDIR)
	$(INSTALL) -d $(INSTALL_LIBDIR)/$(C_DIR)
	(cd c/; $(INSTALL) $(C_OBJ) $(INSTALL_LIBDIR)/$(C_DIR))

uninstall:
	$(foreach f,$(STDLIB_OBJ) $(STDLIB_INTERFACE),$(RM) $(INSTALL_LIBDIR)/$(f))
	$(RM) $(INSTALL_LIBDIR)/$(C_DIR)/$(C_OBJ)

clean:
	rm -f *.epci

