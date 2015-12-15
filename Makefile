include config

.PHONY: all install uninstall clean

all:
	(cd compiler/; $(MAKE))
	(cd lib; $(MAKE))

install:
	(cd compiler; $(MAKE) install)
	(cd lib; $(MAKE) install)

uninstall:
	(cd compiler; $(MAKE) uninstall)
	(cd lib; $(MAKE) uninstall)

clean:
	(cd compiler; $(MAKE) clean)
	(cd lib; $(MAKE) clean)
