include ../config

BIN:=$(COMPILER)

ifeq ($(ENABLE_SIMULATOR), yes)
  BIN:=$(BIN) $(SIMULATOR)
endif

ifeq ($(ENABLE_CTRL2EPT_TRANSLATOR), yes)
  BIN:=$(BIN) $(CTRLNBAC2EPT_TRANSLATOR)
endif

.PHONY: all clean native byte clean debug install

all: $(TARGET)

native:
	$(OCAMLBUILD) $(addsuffix .native,$(BIN))

byte:
	$(OCAMLBUILD) $(addsuffix .byte,$(BIN))

debug:
	$(OCAMLBUILD) $(addsuffix .d.byte,$(BIN))

profile:
	$(OCAMLBUILD) $(addsuffix .p.native,$(BIN))

install: 
	$(INSTALL) -d $(INSTALL_BINDIR)
	$(foreach t,$(BIN),$(INSTALL) $(t).$(TARGET) $(INSTALL_BINDIR)/$(t);)

uninstall:
	$(foreach t,$(BIN),$(RM) $(INSTALL_BINDIR)/$(t);)

clean:
	$(OCAMLBUILD) -clean

.PHONY: doc
doc: $(TARGET)
#	Filter unused modules by scanning built ones:
	find _build -regex '.*.cmi?' -printf '%f\n' \
	   | sed -e '/ocamlbuild/ d; s/\(.*\)\.cmi$$/\u\1/' \
	   | sort > doc.odocl;
	$(OCAMLBUILD) doc.docdir/index.html
