# Makefile,v
# Copyright (c) INRIA 2007-2017

TOP=.
include $(TOP)/config/Makefile

WD=$(shell pwd)
RM=rm

all:
	$(MAKE) -C src all

test: all
	$(MAKE) -C test test

bootstrap:
	$(MAKE) -C src clean
	$(MAKE) -C src DESTDIR=$(WD)/$(TOP)/bootstrap-install all

install: all META.pl
	$(OCAMLFIND) remove pa_llk || true
	./META.pl > META
	$(OCAMLFIND) install pa_llk META local-install/lib/*/*.*

uninstall:
	$(OCAMLFIND) remove pa_llk || true

prereqs:
	(perl -MIPC::System::Simple -e 1 > /dev/null 2>&1) || (echo "MUST install Perl module IPC::System::Simple" && exit -1)
	(perl -MString::ShellQuote -e 1 > /dev/null 2>&1) || (echo "MUST install Perl module String::ShellQuote" && exit -1)

META: META.pl
	./META.pl > META

clean::
	$(MAKE) -C src clean
	$(MAKE) -C test clean
	$(RM) -rf META bootstrap-install local-install

depend:
	$(MAKE) -C src depend
