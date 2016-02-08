COQMODULE    := cmem
COQTHEORIES  := src/*.v

.PHONY: all theories clean

all: theories

sflib: lib/sflib
	make -C lib/sflib

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R src $(COQMODULE)"; \
   echo "-R lib/sflib sflib"; \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

theories: sflib Makefile.coq
	$(MAKE) -f Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
