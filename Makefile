# Makefile,v
# Copyright (c) INRIA 2007-2017

WD=$(shell pwd)
TOP=.
include $(TOP)/config/Makefile

DESTDIR=
RM=rm

LAUNCH=
OCAMLFIND=$(LAUNCH) ocamlfind
NOT_OCAMLFIND=$(LAUNCH) not-ocamlfind
MKCAMLP5=$(LAUNCH) mkcamlp5
SYNTAX := camlp5r

PACKAGES := $(PACKAGES),bos,fmt,pa_ppx.base.link,pa_ppx.deriving_plugins.std
TARGET := pa_llk.cma
OML := ord_MLast.ml llk_migrate.ml
OMLI := ord_MLast.mli
RML := llk_types.ml pa_llk.ml pr_llk.ml comp_llk.ml
RMLI := 
ML := ord_MLast.ml llk_types.ml llk_migrate.ml pa_llk.ml pr_llk.ml comp_llk.ml
CMO := $(ML:.ml=.cmo)
CMI := $(ML:.ml=.cmi)
CMX := $(ML:.ml=.cmx)
CMT := $(ML:.ml=.cmt)
CMTI := $(MLI:.mli=.cmti)

OCAMLCFLAGS := $(OCAMLCFLAGS) -linkall

all: $(TARGET) $(TARGET:.cma=.cmxa) camlp5.pa_llk camlp5.pa_llk.opt
	$(MAKE) DESTDIR=$(WD)/$(TOP)/local-install/ install

test:: all
	make -C test clean all-tests

doc: $(CMT) $(CMTI)

camlp5.pa_llk: $(TARGET)
	$(MKCAMLP5) -verbose -package fmt,bos,camlp5.pa_r,camlp5.pr_r,pa_ppx.base $(TARGET) -o $@

camlp5.pa_llk.opt: $(TARGET:.cma=.cmxa)
	$(MKCAMLP5).opt -verbose -package fmt,bos,camlp5.pa_r,camlp5.pr_r,pa_ppx.base $(TARGET:.cma=.cmxa) -o $@

META: META.pl
	./META.pl > META

install::
	mkdir -p $(DESTDIR)/lib
	./META.pl $(DESTDIR)/lib > META
	$(NOT_OCAMLFIND) reinstall-if-diff pa_llk -destdir $(DESTDIR)/lib META $(TARGET) $(TARGET:.cma=.cmxa) $(TARGET:.cma=.a) $(CMI) $(wildcard *.cmt*)
	$(RM) -f META

clean::
	rm -rf META camlp5.pa_llk* local-install
	make -C test clean

$(TARGET): $(CMO)
	$(OCAMLFIND) ocamlc $(DEBUG) $(CMO) -a -o $(TARGET)

$(TARGET:.cma=.cmxa): $(CMO:.cmo=.cmx)
	$(OCAMLFIND) ocamlopt $(DEBUG) $(CMO:.cmo=.cmx) -a -o $(TARGET:.cma=.cmxa)

$(TARGET): $(CMO)
$(TARGET:.cma=.cmxa): $(CMO:.cmo=.cmx)

IMPORT_OCAMLFLAGS = 	-ppopt -pa_import-package -ppopt $(PACKAGES) \
	-ppopt -pa_import-I -ppopt . \

ord_MLast.cmo: ord_MLast.ml
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import -syntax camlp5o -c $<

ord_MLast.cmi: ord_MLast.mli
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import -syntax camlp5o -c $<

ord_MLast.cmx: ord_MLast.ml
	$(OCAMLFIND) ocamlopt $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import -syntax camlp5o -c $<

llk_migrate.cmo: llk_migrate.ml
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import,pa_ppx_migrate -syntax camlp5o -c $<

llk_migrate.cmi: llk_migrate.mli
	$(OCAMLFIND) ocamlc $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import,pa_ppx_migrate -syntax camlp5o -c $<

llk_migrate.cmx: llk_migrate.ml
	$(OCAMLFIND) ocamlopt $(OCAMLCFLAGS) $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import,pa_ppx_migrate -syntax camlp5o -c $<


EXTERNAL := $(shell $(OCAMLFIND) query -predicates byte -format '%m' $(PACKAGES) | grep local-install)
$(CMO) $(CMI) $(CMX): $(EXTERNAL)

depend::
	echo "$(CMO) $(CMI) $(CMX): $(EXTERNAL)" > .depend.NEW
	$(OCAMLFIND) ocamldep $(IMPORT_OCAMLFLAGS) -package $(PACKAGES),pa_ppx.import,pa_ppx_migrate -syntax camlp5o $(OML) $(OMLI) >> .depend.NEW
	$(OCAMLFIND) ocamldep -package $(PACKAGES) -syntax camlp5r $(RML) $(RMLI) >> .depend.NEW
	mv .depend.NEW .depend

-include .depend
