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
	-rm -rf _build/

clean-examples:
	find examples -name "*.lpo"|xargs rm
