WD=$(shell pwd)
TOP=../..
include $(TOP)/config/Makefile

LAUNCHMODE ?= "--local"
LAUNCH=env TOP=$(WD)/$(TOP) $(WD)/$(TOP)/tools/LAUNCH $(LAUNCHMODE)
OCAMLFIND=$(LAUNCH) ocamlfind
NOT_OCAMLFIND=$(LAUNCH) not-ocamlfind
SYNTAX := camlp5o

PACKAGES := $(PACKAGES),ounit2,pa_llk_compiler,camlp5,pa_llk_runtime,pa_ppx.runtime_fat,pa_ppx.testutils,str,pa_ppx.deriving_plugins.std,pa_llk_compiler.link,camlp5.extend,fmt,camlp5.extprint,camlp5.extend,camlp5.pprintf,pcre

all: acme acme.opt

acme: acmelexer.cmo acme.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkpkg -syntax camlp5r $^ -o $@

acme.opt: acmelexer.cmx acme.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -linkpkg -syntax camlp5r $^ -o $@

test:: all
	set -e; for i in examples/cmu/*.acmetest; do ./acme $$i; done

.SUFFIXES: .mll .ml .cmo .cmx

acmelexer.cmo: acmelexer.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5o -c $<

acmelexer.cmx: acmelexer.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -syntax camlp5o -c $<

acme.cmo: acme.ml
	$(NOT_OCAMLFIND) preprocess -package $(PACKAGES),camlp5.pr_r -syntax camlp5r -ppopt -llk-report-verbose $< > $<.ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -i -c $<.ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -c $<

acme.cmx: acme.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -syntax camlp5r -c $<

.mll.ml:
	ocamllex $<

clean::
	rm -f acme acme.opt *.cm* *.o acmelexer.ml


depend::
	$(OCAMLFIND) ocamldep -package $(PACKAGES) -syntax camlp5o acmelexer.ml > .depend.NEW || true
	$(OCAMLFIND) ocamldep -package $(PACKAGES) -syntax camlp5r acme.ml >> .depend.NEW \
		&& mv .depend.NEW .depend

-include .depend
