WD=$(shell pwd)
TOP=..
include $(TOP)/config/Makefile

LAUNCHMODE ?= "--local"
LAUNCH=env TOP=$(WD)/$(TOP) $(WD)/$(TOP)/tools/LAUNCH $(LAUNCHMODE)
OCAMLFIND=$(LAUNCH) ocamlfind
NOT_OCAMLFIND=$(LAUNCH) not-ocamlfind
SYNTAX := camlp5o

PACKAGES := $(PACKAGES),ounit2,pa_llk_compiler,camlp5,pa_llk_runtime,pa_ppx.runtime_fat,pa_ppx.testutils,str,pa_ppx.deriving_plugins.std,pa_llk_compiler.link,camlp5.extend
TESTS = simple_otest regexp_otest external_otest infer_otest self_otest bug_fifo_rtest \
 r2official_test o2official_test error_rtest synpred_rtest hoisted_sempred_rtest longident_rtest unused_rtest \
 revised_rtest \
 llkr2official_test \
 original_rtest \
 llko2official_test

ERROR_TESTS = parse_error_test
SUBDIRS = calc abnf acme abb antlr cminus c alef

RML = bug_fifo_rtest.ml  original_rtest.ml  revised_rtest.ml \
	papr_test_matrix.ml \
	o2official_test.ml \
	r2official_test.ml \
	llko2official_test.ml \
	llkr2official_test.ml \
	error_rtest.ml \
	synpred_rtest.ml \
	hoisted_sempred_rtest.ml \
	longident_rtest.ml \
	unused_rtest.ml

OML = external_otest.ml  regexp_otest.ml  simple_otest.ml \
	infer_otest.ml	   self_otest.ml


test:: $(TESTS)
	set -e; for i in $(SUBDIRS); do $(MAKE) -C $$i all test; done

all: simple_otest.exe regexp_otest.exe external_otest.exe infer_otest.exe self_otest.exe \
	bug_fifo_rtest.exe revised_rtest.exe original_rtest.exe \
	r2official_test.exe o2official_test.exe llkr2official_test.exe llko2official_test.exe \
	error_rtest.exe synpred_rtest.exe hoisted_sempred_rtest.exe longident_rtest.exe unused_rtest.exe

%test: %test.exe
	mkdir -p _build
	./$<

%_otest.exe: %_otest.cmo
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.pa_o.link -syntax $(SYNTAX) -linkpkg -linkall -o $@ $<

%_otest.cmo: %_otest.ml
	$(NOT_OCAMLFIND) preprocess -package $(PACKAGES),camlp5.pr_o -syntax $(SYNTAX) -ppopt -llk-report-verbose $< > $<.ppo.ml
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES) -syntax $(SYNTAX) -i -c $<.ppo.ml
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES) -syntax $(SYNTAX) -c $<

%_rtest: %_rtest.exe
	mkdir -p _build
	./$<

%_rtest.exe: %_rtest.cmo
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.pa_o.link -syntax camlp5r -linkpkg -linkall -o $@ $<

%_rtest.cmo: %_rtest.ml
	$(NOT_OCAMLFIND) preprocess -package $(PACKAGES),camlp5.pr_o -syntax camlp5r -ppopt -llk-report-verbose $< > $<.ppo.ml
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES) -syntax camlp5o -i -c $<.ppo.ml
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES) -syntax camlp5r -c $<

r2official_test.exe: papr_test_matrix.cmo r2official_test.cmo
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.macro,camlp5.pr_official.link,camlp5.pa_r.link -syntax camlp5r -linkall -linkpkg $^ -o $@ 

r2official_test.cmo: r2official_test.ml papr_test_matrix.cmi
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.macro,camlp5.pr_official.link -syntax camlp5r -c $<

o2official_test.exe: papr_test_matrix.cmo o2official_test.cmo
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.macro,camlp5.pr_official.link,camlp5.pa_o.link -syntax camlp5r -linkall -linkpkg $^ -o $@ 

o2official_test.cmo: o2official_test.ml papr_test_matrix.cmi
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.macro,camlp5.pr_official.link -syntax camlp5r -c $<

llkr2official_test.exe: papr_test_matrix.cmo revised_rtest.cmo llkr2official_test.cmo
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.macro,camlp5.pr_official.link,camlp5.pa_r.link -syntax camlp5r -linkall -linkpkg $^ -o $@ 

llkr2official_test.cmo: llkr2official_test.ml papr_test_matrix.cmi
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.macro,camlp5.pr_official.link -syntax camlp5r -c $<

llko2official_test.exe: papr_test_matrix.cmo original_rtest.cmo llko2official_test.cmo
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.macro,camlp5.pr_official.link -syntax camlp5r -linkall -linkpkg $^ -o $@ 

llko2official_test.cmo: llko2official_test.ml papr_test_matrix.cmi
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.macro,camlp5.pr_official.link -syntax camlp5r -c $<

papr_test_matrix.cmi papr_test_matrix.cmo: papr_test_matrix.ml
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) -package $(PACKAGES),camlp5.macro -syntax camlp5r -c $<

.PRECIOUS: %test.cmo %test.cmo *.exe *.cmo

clean::
	rm -rf *.cm* *.ppo* *.exe _build
	set -e; for i in $(SUBDIRS); do $(MAKE) -C $$i clean; done

depend::
	$(OCAMLFIND) ocamldep -package $(PACKAGES),camlp5.macro -syntax camlp5o $(OML) >> .depend.NEW
	$(OCAMLFIND) ocamldep -package $(PACKAGES),camlp5.macro -syntax camlp5r $(RML) >> .depend.NEW
	mv .depend.NEW .depend
	set -e; for i in $(SUBDIRS); do $(MAKE) -C $$i all depend; done

-include .depend
