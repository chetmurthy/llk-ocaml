# Makefile,v
# Copyright (c) INRIA 2007-2017

TOP=.
include $(TOP)/config/Makefile

WD=$(shell pwd)
RM=rm
CP=cp

all: bootstrap-install
	$(MAKE) -C src all
	$(MAKE) -C cmds all

world:
	$(RM) -rf $(WD)/$(TOP)/bootstrap-install
	$(RM) -rf $(WD)/$(TOP)/local-install
	$(MAKE) bootstrap
	$(MAKE) all

test: all
	$(MAKE) -C test test

bootstrap:
	$(MAKE) -C bootstrap-src DESTDIR=$(WD)/$(TOP)/bootstrap-install all

install: all META.pl
	$(OCAMLFIND) remove pa_llk || true
	./META.pl > META
	$(OCAMLFIND) install pa_llk META local-install/lib/*/*.*

new_sources:
	$(RM) -rf bootstrap-src.new
	mkdir bootstrap-src.new
	tar --exclude=parse_bootstrapped.ml --exclude="*.ppo.ml" --exclude="*.cm*" --exclude="*.opt" --exclude="*.o" --exclude="*.a" --exclude="*compiler" -C src -cf - pa_llk runtime | tar -C bootstrap-src.new -xBf -
	$(CP) src/pa_llk/parse_bootstrapped.ml.ppo.ml bootstrap-src.new/pa_llk/parse_bootstrapped.ml

compare_sources: new_sources
	diff -Bwiu --recursive  --exclude="*.cm*" --exclude="*.opt" --exclude="*.o" --exclude="*.a" --exclude="*compiler" bootstrap-src bootstrap-src.new

promote_sources: new_sources
	$(RM) -rf bootstrap-src/{pa_llk,runtime}
	tar -C bootstrap-src.new -cf - . | tar -C bootstrap-src -xf -

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
	$(RM) -rf META local-install bootstrap-src.new

realclean:: clean
	$(MAKE) -C bootstrap-src clean
	$(RM) -rf bootstrap-install

depend:
	$(MAKE) -C src depend
