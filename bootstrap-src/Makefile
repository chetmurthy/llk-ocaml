# Makefile,v
# Copyright (c) INRIA 2007-2017

TOP=..
include $(TOP)/config/Makefile

WD=$(shell pwd)
RM=rm
DESTDIR ?= $(WD)/$(TOP)/local-install
LAUNCHMODE = "--bootstrap"
EXTRAPACKAGES=,

SYSDIRS= runtime pa_llk

all:
	set -e; for i in $(SYSDIRS); do cd $$i; \
	$(MAKE) DESTDIR=$(DESTDIR) LAUNCHMODE=$(LAUNCHMODE) EXTRAPACKAGES=$(EXTRAPACKAGES) all; \
	cd ..; done

clean::
	set -e; for i in $(SYSDIRS); do cd $$i; $(MAKE) clean; cd ..; done

depend:
	set -e; for i in $(SYSDIRS); do cd $$i; $(MAKE) depend; cd ..; done
