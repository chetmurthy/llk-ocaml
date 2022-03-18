# Makefile,v
# Copyright (c) INRIA 2007-2017

WD=$(shell pwd)
TOP = ../..
include $(TOP)/config/Makefile

DESTDIR ?= $(WD)/$(TOP)/local-install
RM=rm

LAUNCHMODE ?= "--bootstrap"
EXTRAPACKAGES ?= "pa_llk_compiler,pa_llk_runtime"
LAUNCH=env TOP=$(WD)/$(TOP) $(WD)/$(TOP)/tools/LAUNCH $(LAUNCHMODE)
OCAMLFIND=$(LAUNCH) ocamlfind
NOT_OCAMLFIND=$(LAUNCH) not-ocamlfind
MKCAMLP5=$(LAUNCH) mkcamlp5
SYNTAX := camlp5r

PACKAGES := $(PACKAGES),bos,fmt,pa_ppx.base.link,pa_ppx.deriving_plugins.std,$(EXTRAPACKAGES)
TARGET := pa_llk_compiler.cma
OML := brzozowski2.ml ord_MLast.ml llk_migrate.ml parse_bootstrapped.ml
OMLI := ord_MLast.mli
RML := llk_regexps.ml llk_types.ml parse_gram.ml print_gram.ml comp_llk.ml pa_llk.ml
RMLI := 
ML := brzozowski2.ml ord_MLast.ml llk_regexps.ml llk_types.ml llk_migrate.ml parse_gram.ml parse_bootstrapped.ml print_gram.ml comp_llk.ml pa_llk.ml
CMO := $(ML:.ml=.cmo)
CMI := $(ML:.ml=.cmi)
CMX := $(ML:.ml=.cmx)
CMT := $(ML:.ml=.cmt)
CMTI := $(MLI:.mli=.cmti)

all: $(TARGET) $(TARGET:.cma=.cmxa) camlp5.pa_llk_compiler camlp5.pa_llk_compiler.opt
	$(MAKE) DESTDIR=$(DESTDIR) install

test:: all

doc: $(CMT) $(CMTI)

camlp5.pa_llk_compiler: $(TARGET)
	$(MKCAMLP5) -verbose -package fmt,bos,camlp5.pa_r,camlp5.pr_r,pa_ppx.base $(TARGET) -o $@

camlp5.pa_llk_compiler.opt: $(TARGET:.cma=.cmxa)
	$(MKCAMLP5).opt -verbose -package fmt,bos,camlp5.pa_r,camlp5.pr_r,pa_ppx.base $(TARGET:.cma=.cmxa) -o $@

META: META.pl
	./META.pl > META

install::
	mkdir -p $(DESTDIR)/lib
	./META.pl $(DESTDIR)/lib > META
	$(NOT_OCAMLFIND) reinstall-if-diff pa_llk_compiler -destdir $(DESTDIR)/lib META $(TARGET) $(TARGET:.cma=.cmxa) $(TARGET:.cma=.a) $(CMI) $(wildcard *.cmt*)
	$(RM) -f META

clean::
	rm -rf META camlp5.pa_llk_compiler*

$(TARGET): $(CMO)
	$(OCAMLFIND) ocamlc $(DEBUG) $(CMO) -a -o $(TARGET)

$(TARGET:.cma=.cmxa): $(CMO:.cmo=.cmx)
	$(OCAMLFIND) ocamlopt $(DEBUG) $(CMO:.cmo=.cmx) -a -o $(TARGET:.cma=.cmxa)

$(TARGET): $(CMO)
$(TARGET:.cma=.cmxa): $(CMO:.cmo=.cmx)

IMPORT_OCAMLFLAGS = 	-ppopt -pa_import-package -ppopt $(PACKAGES) \
	-ppopt -pa_import-I -ppopt . \

ord_MLast.cmo: ord_MLast.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import -syntax camlp5o -c $<

ord_MLast.cmi: ord_MLast.mli
	$(OCAMLFIND) ocamlc $(DEBUG) $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import -syntax camlp5o -c $<

ord_MLast.cmx: ord_MLast.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import -syntax camlp5o -c $<

llk_migrate.cmo: llk_migrate.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import,pa_ppx_migrate -syntax camlp5o -c $<

llk_migrate.cmi: llk_migrate.mli
	$(OCAMLFIND) ocamlc $(DEBUG) $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import,pa_ppx_migrate -syntax camlp5o -c $<

llk_migrate.cmx: llk_migrate.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import,pa_ppx_migrate -syntax camlp5o -c $<

brzozowski2.cmo: brzozowski2.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import,pa_ppx_migrate -syntax camlp5o -c $<

brzozowski2.cmi: brzozowski2.mli
	$(OCAMLFIND) ocamlc $(DEBUG) $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import,pa_ppx_migrate -syntax camlp5o -c $<

brzozowski2.cmx: brzozowski2.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import,pa_ppx_migrate -syntax camlp5o -c $<

parse_bootstrapped.cmo: parse_bootstrapped.ml
	$(NOT_OCAMLFIND) preprocess $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import,pa_ppx_migrate,camlp5.pr_o -syntax camlp5o $< > parse_bootstrapped.ml.ppo.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import,pa_ppx_migrate -syntax camlp5o -c $<

parse_bootstrapped.cmi: parse_bootstrapped.mli
	$(OCAMLFIND) ocamlc $(DEBUG) $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import,pa_ppx_migrate -syntax camlp5o -c $<

parse_bootstrapped.cmx: parse_bootstrapped.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import,pa_ppx_migrate -syntax camlp5o -c $<

EXTERNAL := $(shell $(OCAMLFIND) query -predicates byte -format '%m' $(PACKAGES) | grep local-install)
$(CMO) $(CMI) $(CMX): $(EXTERNAL)

depend::
	echo "$(CMO) $(CMI) $(CMX): $(EXTERNAL)" > .depend.NEW
	$(OCAMLFIND) ocamldep $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import,pa_ppx_migrate -syntax camlp5o $(OML) $(OMLI) >> .depend.NEW
	$(OCAMLFIND) ocamldep -package $(PACKAGES) -syntax camlp5r $(RML) $(RMLI) >> .depend.NEW
	mv .depend.NEW .depend

-include .depend
