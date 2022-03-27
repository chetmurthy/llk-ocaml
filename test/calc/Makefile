WD=$(shell pwd)
TOP=../..
include $(TOP)/config/Makefile

LAUNCHMODE ?= "--local"
LAUNCH=env TOP=$(WD)/$(TOP) $(WD)/$(TOP)/tools/LAUNCH $(LAUNCHMODE)
OCAMLFIND=$(LAUNCH) ocamlfind
NOT_OCAMLFIND=$(LAUNCH) not-ocamlfind
SYNTAX := camlp5o

PACKAGES := $(PACKAGES),ounit2,pa_llk_compiler,camlp5,pa_llk_runtime,pa_ppx.runtime_fat,pa_ppx.testutils,str,pa_ppx.deriving_plugins.std,pa_llk_compiler.link,camlp5.extend,fmt,camlp5.extprint,camlp5.extend,camlp5.pprintf,pcre

all: calc calc.opt

calc: calclexer.cmo calc.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -linkpkg -syntax camlp5r $^ -o $@

calc.opt: calclexer.cmx calc.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -linkpkg -syntax camlp5r $^ -o $@

test:: all
	echo '1+1 ; 1 - 1; 1 + (2 * 3)' | ./calc

.SUFFIXES: .mll .ml .cmo .cmx

calclexer.cmo: calclexer.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5o -c $<

calclexer.cmx: calclexer.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -syntax camlp5o -c $<

calc.cmo: calc.ml
	$(OCAMLFIND) ocamlc $(DEBUG) -package $(PACKAGES) -syntax camlp5r -c $<

calc.cmx: calc.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) -package $(PACKAGES) -syntax camlp5r -c $<

.mll.ml:
	ocamllex $<

clean::
	rm -f calc calc.opt *.cm* *.o calclexer.ml


depend::
	$(OCAMLFIND) ocamldep $(DEBUG) -package $(PACKAGES) -syntax camlp5o calclexer.ml > .depend.NEW || true
	$(OCAMLFIND) ocamldep $(DEBUG) -package $(PACKAGES) -syntax camlp5r calc.ml >> .depend.NEW \
		&& mv .depend.NEW .depend

-include .depend
