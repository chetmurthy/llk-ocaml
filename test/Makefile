WD=$(shell pwd)
TOP=..
include $(TOP)/config/Makefile

LAUNCHMODE ?= "--local"
LAUNCH=env TOP=$(WD)/$(TOP) $(WD)/$(TOP)/tools/LAUNCH $(LAUNCHMODE)
OCAMLFIND=$(LAUNCH) ocamlfind
NOT_OCAMLFIND=$(LAUNCH) not-ocamlfind
SYNTAX := camlp5o

PACKAGES := $(PACKAGES),ounit2,pa_llk_compiler,camlp5,pa_llk_runtime,pa_ppx.runtime_fat,pa_ppx.testutils,str,camlp5.pa_o.link,pa_ppx.deriving_plugins.std,pa_llk_compiler.link
TESTS = simple_otest regexp_otest external_otest infer_otest self_otest bug_fifo_rtest revised_rtest original_rtest
ERROR_TESTS = parse_error_test

test:: $(TESTS)

all: simple_otest.exe regexp_otest.exe external_otest.exe infer_otest.exe self_otest.exe bug_fifo_rtest.exe revised_rtest.exe original_rtest.exe

%_otest: %_otest.exe
	mkdir -p _build
	./$<

%_otest.exe: %_otest.cmo
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES) -syntax $(SYNTAX) -linkpkg -linkall -o $@ $<

%_otest.cmo: %_otest.ml
	$(NOT_OCAMLFIND) preprocess -package $(PACKAGES),camlp5.pr_o -syntax $(SYNTAX) -ppopt -llk-report-verbose $< > $<.ppo.ml
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES) -syntax $(SYNTAX) -i -c $<.ppo.ml
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES) -syntax $(SYNTAX) -c $<

%_rtest: %_rtest.exe
	mkdir -p _build
	./$<

%_rtest.exe: %_rtest.cmo
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES) -syntax camlp5r -linkpkg -linkall -o $@ $<

%_rtest.cmo: %_rtest.ml
	$(NOT_OCAMLFIND) preprocess -package $(PACKAGES),camlp5.pr_r -syntax camlp5r -ppopt -llk-report-verbose $< > $<.ppo.ml
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES) -syntax camlp5r -i -c $<.ppo.ml
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES) -syntax camlp5r -c $<

.PRECIOUS: %_otest.cmo %_rtest.cmo

clean::
	rm -rf *.cm* *.ppo* *.exe _build
