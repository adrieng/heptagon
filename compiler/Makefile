
BUILD:= _build
OCAMLBUILD:=ocamlbuild
COMPILER:=heptc

TARGET:=byte

.PHONY: all opt byte debug profile clean

all: $(TARGET)

opt:
	$(OCAMLBUILD) $(COMPILER).native
byte:
	$(OCAMLBUILD) $(COMPILER).byte

debug:
	$(OCAMLBUILD) $(COMPILER).d.byte
profile:
	$(OCAMLBUILD) $(COMPILER).p.native


clean:
	$(OCAMLBUILD).native -clean
