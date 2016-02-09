COQMODULE    := cmem
COQTHEORIES  := src/*/*.v

.PHONY: all theories clean

all: theories

sflib: lib/sflib
	make -C lib/sflib

paco: lib/paco/src
	make -C lib/paco/src

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R lib/sflib sflib"; \
   echo "-R lib/paco/src Paco"; \
   \
   echo "-R src/mem $(COQMODULE)"; \
   echo "-R src/lang $(COQMODULE)"; \
   echo "-R src/reorder $(COQMODULE)"; \
   \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

theories: sflib paco Makefile.coq
	$(MAKE) -f Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
