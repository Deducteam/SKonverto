DUNE ?= dune

.PHONY: bin install doc uninstall clean
bin:
	$(DUNE) build

install:
	$(DUNE) install

doc:
	$(DUNE) build @doc

uninstall:
	$(DUNE) uninstall

clean:
	-rm -r _build/