WD=$(shell pwd)
TOP=../..
include $(TOP)/config/Makefile

LAUNCHMODE ?= "--local"
LAUNCH=env TOP=$(WD)/$(TOP) $(WD)/$(TOP)/tools/LAUNCH $(LAUNCHMODE)
OCAMLFIND=$(LAUNCH) ocamlfind
NOT_OCAMLFIND=$(LAUNCH) not-ocamlfind
SYNTAX := camlp5o

PACKAGES := $(PACKAGES),ounit2,pa_llk_compiler,camlp5,pa_llk_runtime,pa_ppx.runtime_fat,pa_ppx.testutils,str,pa_ppx.deriving_plugins.std,pa_llk_compiler.link,camlp5.extend,fmt,camlp5.extprint,camlp5.extend,camlp5.pprintf,pcre

all: abnf abnf.opt

abnf: abnflexer.cmo abnf.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkpkg -syntax camlp5r $^ -o $@

abnf.opt: abnflexer.cmx abnf.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -linkpkg -syntax camlp5r $^ -o $@

test:: all
	cat examples/iri.abnf | ./abnf

.SUFFIXES: .mll .ml .cmo .cmx

abnflexer.cmo: abnflexer.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5o -c $<

abnflexer.cmx: abnflexer.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -syntax camlp5o -c $<

abnf.cmo: abnf.ml
	$(NOT_OCAMLFIND) preprocess -package $(PACKAGES),camlp5.pr_r -syntax camlp5r -ppopt -llk-report-verbose $< > $<.ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -i -c $<.ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -c $<

abnf.cmx: abnf.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -syntax camlp5r -c $<

.mll.ml:
	ocamllex $<

clean::
	rm -f abnf abnf.opt *.cm* *.o abnflexer.ml


depend::
	$(OCAMLFIND) ocamldep -package $(PACKAGES) -syntax camlp5o abnflexer.ml > .depend.NEW || true
	$(OCAMLFIND) ocamldep -package $(PACKAGES) -syntax camlp5r abnf.ml >> .depend.NEW \
		&& mv .depend.NEW .depend

-include .depend
