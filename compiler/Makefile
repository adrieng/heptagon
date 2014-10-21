include ../config

BIN:=heptc.$(TARGET)

ifeq ($(ENABLE_SIMULATOR), yes)
  BIN:=$(BIN) hepts.$(TARGET)
endif

ifeq ($(ENABLE_CTRL2EPT), yes)
  BIN:=$(BIN) ctrl2ept.$(TARGET)
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

install: 
	$(INSTALL) -d $(INSTALL_BINDIR)
	$(INSTALL) $(COMPILER).$(TARGET) $(INSTALL_BINDIR)/$(COMPILER)
ifeq ($(ENABLE_SIMULATOR), yes)
	$(INSTALL) $(SIMULATOR).$(TARGET) $(INSTALL_BINDIR)/$(SIMULATOR)
endif

clean:
	$(OCAMLBUILD) -clean

.PHONY: doc
doc: $(TARGET)
#	Filter unused modules by scanning built ones:
	find _build -regex '.*.cmi?' -printf '%f\n' \
	   | sed -e '/ocamlbuild/ d; s/\(.*\)\.cmi$$/\u\1/' \
	   | sort > doc.odocl;
	$(OCAMLBUILD) doc.docdir/index.html
