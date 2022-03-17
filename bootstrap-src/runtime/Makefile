# Makefile,v
# Copyright (c) INRIA 2007-2017

WD=$(shell pwd)
TOP=../..
include $(TOP)/config/Makefile

DESTDIR ?= $(WD)/$(TOP)/local-install
RM=rm

LAUNCHMODE ?= "--bootstrap"
LAUNCH=env TOP=$(TOP) $(TOP)/tools/LAUNCH
OCAMLFIND=$(LAUNCH) ocamlfind
NOT_OCAMLFIND=$(LAUNCH) not-ocamlfind

PACKAGES = rresult,fmt,camlp5,pa_ppx.utils,$(EXTRAPACKAGES)
TARGET = pa_llk_runtime.cma
ML = llk_runtime.ml
MLI =
CMO = $(ML:.ml=.cmo)
CMI = $(ML:.ml=.cmi)
CMX = $(ML:.ml=.cmx)
CMT = $(ML:.ml=.cmt)
CMTI = $(MLI:.mli=.cmti)

OCAMLCFLAGS := $(OCAMLCFLAGS) -for-pack Pa_llk_runtime -linkall

all: $(TARGET) $(TARGET:.cma=.cmxa)
	$(MAKE) DESTDIR=$(DESTDIR) install

doc: $(CMT) $(CMTI)

pa_llk_runtime.cmo: $(CMO)
	$(OCAMLFIND) ocamlc $(DEBUG) -pack -o pa_llk_runtime.cmo $^

pa_llk_runtime.cmx: $(CMO:.cmo=.cmx)
	$(OCAMLFIND) ocamlopt $(DEBUG) -pack -o pa_llk_runtime.cmx $^

META: META.pl
	./META.pl > META
install::
	mkdir -p $(DESTDIR)/lib
	./META.pl $(DESTDIR)/lib > META
	$(NOT_OCAMLFIND) reinstall-if-diff pa_llk_runtime -destdir $(DESTDIR)/lib META $(TARGET) $(TARGET:.cma=.cmxa) $(TARGET:.cma=.a) pa_llk_runtime.cmx pa_llk_runtime.cmi $(wildcard *.cmt*)
	$(RM) -f META

clean::
	rm -rf META

$(TARGET): pa_llk_runtime.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) pa_llk_runtime.cmo -a -o $(TARGET)

$(TARGET:.cma=.cmxa): pa_llk_runtime.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) pa_llk_runtime.cmx -a -o $(TARGET:.cma=.cmxa)

$(TARGET): $(CMO)
$(TARGET:.cma=.cmxa): $(CMO:.cmo=.cmx)

EXTERNAL = $(shell $(OCAMLFIND) query -predicates byte -format '%m' $(PACKAGES) | grep local-install)
$(CMO) $(CMI) $(CMX): $(EXTERNAL)

depend::
	echo "$(CMO) $(CMI) $(CMX): $(EXTERNAL)" > .depend.NEW
	$(OCAMLFIND) ocamldep -package $(PACKAGES) -syntax camlp5r llk_runtime.ml >> .depend.NEW \
		&& mv .depend.NEW .depend

-include .depend
