COQMODULE    := cmem
COQTHEORIES  := lib/promising-lib/lib/sflib/*.v \
	lib/promising-lib/src/*.v \
	src/*/*.v

.PHONY: all theories clean

all: quick

build: promising-lib Makefile.coq
	$(MAKE) -f Makefile.coq all

quick: promising-lib-quick Makefile.coq
	$(MAKE) -f Makefile.coq quick

promising-lib: lib/promising-lib
	$(MAKE) -C lib/promising-lib

promising-lib-quick: lib/promising-lib
	$(MAKE) -C lib/promising-lib quick

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R lib/promising-lib/lib/sflib sflib"; \
   echo "-R lib/promising-lib/src PromisingLib"; \
   \
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
