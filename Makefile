.PHONY: all install

all:
	(cd compiler/; $(MAKE))
	(cd lib; $(MAKE))

install:
	(cd compiler; $(MAKE) install)
	(cd lib; $(MAKE) install)

clean:
	(cd compiler; $(MAKE) clean)
	(cd lib; $(MAKE) clean)
