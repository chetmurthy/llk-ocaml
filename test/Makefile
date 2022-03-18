WD=$(shell pwd)
TOP=..
include $(TOP)/config/Makefile

LAUNCHMODE ?= "--local"
LAUNCH=env TOP=$(WD)/$(TOP) $(WD)/$(TOP)/tools/LAUNCH $(LAUNCHMODE)
OCAMLFIND=$(LAUNCH) ocamlfind
NOT_OCAMLFIND=$(LAUNCH) not-ocamlfind
SYNTAX := camlp5o

PACKAGES := $(PACKAGES),ounit2,pa_llk_compiler,camlp5,pa_llk_runtime,pa_ppx.runtime_fat,pa_ppx.testutils,str,camlp5.pa_o.link,pa_ppx.deriving_plugins.std,pa_llk_compiler.link
TESTS = simple_test regexp_test external_test infer_test self_test revised_test
ERROR_TESTS = parse_error_test

test:: $(TESTS)

all: simple_test.exe regexp_test.exe external_test.exe infer_test.exe self_test.exe revised_test.exe

%_test: %_test.exe
	mkdir -p _build
	./$<

%_test.exe: %_test.cmo
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES) -syntax $(SYNTAX) -linkpkg -linkall -o $@ $<

%_test.cmo: %_test.ml
	$(NOT_OCAMLFIND) preprocess -package $(PACKAGES),camlp5.pr_o -syntax $(SYNTAX) $< > $<.ppo.ml
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES) -syntax $(SYNTAX) -i -c $<.ppo.ml
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES) -syntax $(SYNTAX) -c $<

revised_test.cmo: revised_test.ml
	$(NOT_OCAMLFIND) preprocess -package $(PACKAGES),camlp5.pr_r -syntax camlp5r $< > $<.ppo.ml
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES) -syntax camlp5r -i -c $<.ppo.ml
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES) -syntax camlp5r -c $<

.PRECIOUS: %_test.cmo

clean::
	rm -rf *.cm* *.ppo* *.exe _build
