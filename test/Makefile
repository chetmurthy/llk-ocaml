WD=$(shell pwd)
TOP=..
include $(TOP)/config/Makefile

LAUNCH=../tools/LAUNCH
OCAMLFIND=$(LAUNCH) ocamlfind
NOT_OCAMLFIND=$(LAUNCH) not-ocamlfind
SYNTAX := camlp5o

PACKAGES := $(PACKAGES),ounit2,pa_llk_compiler,camlp5,pa_llk_runtime,pa_ppx.runtime_fat,pa_ppx.testutils,str,camlp5.pa_o.link
TESTS = simple_test regexp_test external_test

test:: $(TESTS)

all: simple_test.exe regexp_test.exe external_test.exe

%_test: %_test.exe
	mkdir -p _build
	./$<

%_test.exe: %_test.cmo
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES) -syntax $(SYNTAX) -linkpkg -linkall -o $@ $<

%_test.cmo: %_test.ml
	$(NOT_OCAMLFIND) preprocess -package $(PACKAGES),camlp5.pr_o -syntax $(SYNTAX) $< > $<.ppo.ml
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES) -syntax $(SYNTAX) -i -c $<.ppo.ml
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES) -syntax $(SYNTAX) -c $<

.PRECIOUS: %_test.cmo

clean::
	rm -f *.cm* *.ppo* *.exe
