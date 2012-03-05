include ../config

ifeq ($(ENABLE_SIMULATOR), yes)
BIN:=heptc.$(TARGET) hepts.$(TARGET)
else
BIN:=heptc.$(TARGET)
endif

.PHONY: all clean native byte clean debug install

all: $(TARGET)

native:
ifeq ($(ENABLE_SIMULATOR), yes)
	$(OCAMLBUILD) $(COMPILER).native $(SIMULATOR).native
else
	$(OCAMLBUILD) $(COMPILER).native
endif

byte:
ifeq ($(ENABLE_SIMULATOR), yes)
	$(OCAMLBUILD) $(COMPILER).byte $(SIMULATOR).byte
else
	$(OCAMLBUILD) $(COMPILER).byte
endif

debug:
ifeq ($(ENABLE_SIMULATOR), yes)
	$(OCAMLBUILD) $(COMPILER).d.byte $(SIMULATOR).d.byte
else
	$(OCAMLBUILD) $(COMPILER).d.byte
endif

profile:
ifeq ($(ENABLE_SIMULATOR), yes)
	$(OCAMLBUILD) $(COMPILER).p.native $(SIMULATOR).p.native
else
	$(OCAMLBUILD) $(COMPILER).p.native
endif

install: all
	$(INSTALL) -d $(INSTALL_BINDIR)
	$(INSTALL) $(COMPILER).$(TARGET) $(INSTALL_BINDIR)/$(COMPILER)
ifeq ($(ENABLE_SIMULATOR), yes)
	$(INSTALL) $(COMPILER).$(TARGET) $(INSTALL_BINDIR)/$(SIMULATOR)
endif

clean:
	$(OCAMLBUILD) -clean
