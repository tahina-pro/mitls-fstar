EXTRACT='Nothing'
FLAVOR?=Model

# NOTE: by default, this file DOES NOT verify LowParse. It only
# verifies and tests LowParse examples and unit tests. If you want to
# verify LowParse, then you can explicit set the VERIFY_LOWPARSE
# variable. In that case, F* ulib and KreMLib MUST have been already
# verified beforehand.

# ADL (31 Aug. 2018) Disabling ocaml-all during transition to EverCrypt
all: clean-depend model-all kremlin-all lowparse lowparse-examples #ocaml-all

lowparse:
ifdef VERIFY_LOWPARSE
	+$(MAKE) -C ../lowparse -f Makefile.LowParse
endif

lowparse-clean:
	+$(MAKE) -C ../lowparse clean
	+$(MAKE) -C ../lowparse -f Makefile.LowParse clean

lowparse-examples:
	+$(MAKE) ADMIT_LOWPARSE=1 -C ../lowparse

clean-depend:
	rm -f cache/OCaml/.depend cache/Kremlin/.depend cache/Model/.depend

SHELL=/bin/bash

.PHONY: clean-%
clean-c:
	rm -rf extract/Kremlin-{Library,Internal-Test}/{*.c,*/*.c}

ocaml-%: clean-depend
	+$(MAKE) -f Makefile.OCaml $*

kremlin-%: clean-depend
	+$(MAKE) -f Makefile.Kremlin $*

model-% verify-%: clean-depend
	+$(MAKE) -f Makefile.Model $*

quic-%: clean-depend
	+$(MAKE) -C ../../apps/quicMinusNet $* -k

#ADL (31 Aug. 2018) Disabling ocaml-test during transition to EverCrypt
test: clean-depend model-test kremlin-test quic-test #ocaml-test

clean: ocaml-clean kremlin-clean quic-clean model-clean lowparse-clean
	rm -rf extract/Kremlin extract/OCaml extract/copied

%.fst-in %.fsti-in:
	+$(MAKE) -f Makefile.$(FLAVOR) $@

%.fst-ver %.fsti-ver:
	rm -f cache/Model/$(notdir $(subst -ver,,$@)).checked
	+$(MAKE) -f Makefile.Model cache/Model/$(notdir $(subst -ver,,$@)).checked

todo:
	grep -nH -i -e admit -e assume -e '--lax' -e todo -e magic Make* `find . -regex '.*.fst[i]*'` | grep -v 'assume val'
