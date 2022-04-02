WD=$(shell pwd)
TOP=../..
include $(TOP)/config/Makefile

LAUNCHMODE ?= "--local"
LAUNCH=env TOP=$(WD)/$(TOP) $(WD)/$(TOP)/tools/LAUNCH $(LAUNCHMODE)
OCAMLFIND=$(LAUNCH) ocamlfind
NOT_OCAMLFIND=$(LAUNCH) not-ocamlfind
SYNTAX := camlp5o

PACKAGES := $(PACKAGES),ounit2,pa_llk_compiler,camlp5,pa_llk_runtime,pa_ppx.runtime_fat,pa_ppx.testutils,str,pa_ppx.deriving_plugins.std,pa_llk_compiler.link,camlp5.extend,fmt,camlp5.extprint,camlp5.extend,camlp5.pprintf,pcre

all: abb abb.opt

abb: abblexer.cmo abb.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkpkg -syntax camlp5r $^ -o $@

abb.opt: abblexer.cmx abb.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -linkpkg -syntax camlp5r $^ -o $@

test:: all
	./abb examples/robdata.sys

.SUFFIXES: .mll .ml .cmo .cmx

abblexer.cmo: abblexer.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5o -c $<

abblexer.cmx: abblexer.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -syntax camlp5o -c $<

abb.cmo: abb.ml
	$(NOT_OCAMLFIND) preprocess -package $(PACKAGES),camlp5.pr_r -syntax camlp5r -ppopt -llk-report-verbose $< > $<.ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -i -c $<.ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -c $<

abb.cmx: abb.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -syntax camlp5r -c $<

.mll.ml:
	ocamllex $<

clean::
	rm -f abb abb.opt *.cm* *.o abblexer.ml


depend::
	$(OCAMLFIND) ocamldep -package $(PACKAGES) -syntax camlp5o abblexer.ml > .depend.NEW || true
	$(OCAMLFIND) ocamldep -package $(PACKAGES) -syntax camlp5r abb.ml >> .depend.NEW \
		&& mv .depend.NEW .depend

-include .depend
