COQMODULE    := cmem
COQTHEORIES  := lib/sflib/*.v src/*/*.v

.PHONY: all theories clean

all: quick

build: sflib Makefile.coq
	$(MAKE) -f Makefile.coq all

quick: sflib-quick Makefile.coq
	$(MAKE) -f Makefile.coq quick

sflib: lib/sflib
	$(MAKE) -C lib/sflib

sflib-quick: lib/sflib
	$(MAKE) -C lib/sflib quick

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R lib/sflib sflib"; \
   \
   echo "-R src/lib $(COQMODULE)"; \
   echo "-R src/lang $(COQMODULE)"; \
   echo "-R src/while $(COQMODULE)"; \
   echo "-R src/prop $(COQMODULE)"; \
   echo "-R src/opt $(COQMODULE)"; \
   echo "-R src/drf $(COQMODULE)"; \
   echo "-R src/invariant $(COQMODULE)"; \
   \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f _CoqProject Makefile.coq
