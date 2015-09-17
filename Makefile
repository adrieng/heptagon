include config

.PHONY: all install

all:
	(cd compiler/; $(MAKE))
	(cd lib; $(MAKE))

install:
	(cd compiler; $(MAKE) install)
	(cd lib; $(MAKE) install)
	$(INSTALL) tools/$(BZREAX) $(INSTALL_BINDIR)

uninstall:
	(cd compiler; $(MAKE) uninstall)
	(cd lib; $(MAKE) uninstall)
	$(RM) $(INSTALL_BINDIR)/$(BZREAX)

clean:
	(cd compiler; $(MAKE) clean)
	(cd lib; $(MAKE) clean)
