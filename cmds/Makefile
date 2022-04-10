WD=$(shell pwd)
TOP=..
include $(TOP)/config/Makefile

LAUNCHMODE ?= "--local"
LAUNCH=env TOP=$(WD)/$(TOP) $(WD)/$(TOP)/tools/LAUNCH $(LAUNCHMODE)
OCAMLFIND=$(LAUNCH) ocamlfind
NOT_OCAMLFIND=$(LAUNCH) not-ocamlfind
MKCAMLP5=$(LAUNCH) mkcamlp5
SYNTAX := camlp5o

PACKAGES := $(PACKAGES),ounit2,pa_llk_compiler,camlp5,pa_llk_runtime,pa_ppx.runtime_fat,pa_ppx.testutils,str,pa_ppx.deriving_plugins.std,pa_llk_compiler.link,camlp5.extend

RML = 

OML = standalone.ml

all: standalone-o.opt standalone-r.opt \
	standalone-o.exe standalone-r.exe \

#RECORD=perf record --call-graph dwarf -- 
RECORD=perf record --call-graph dwarf,32768 -i -e cycles:u -- 

perf: standalone-r.opt
	$(RECORD) ./standalone-r.opt firstk xx.ml alg_attributes_no_anti

FGDIR=$(HOME)/Hack/Github/brendangregg/FlameGraph

flamegraph::
	perf script | $(FGDIR)/stackcollapse-perf.pl | $(FGDIR)/flamegraph.pl > perf-flamegraph.svg

report::
	perf report --children

R_PACKAGES=bos,fmt,cmdliner,unix,compiler-libs.common,camlp5,camlp5.pr_r.link,camlp5.pa_r.link,camlp5.extfun,camlp5.extend,camlp5.pprintf,camlp5.quotations.link,ounit2,pa_ppx.runtime_fat,pa_ppx.testutils,str,pa_ppx.deriving_plugins.std,camlp5.extend,pa_llk_compiler.link,camlp5,pa_llk_runtime

O_PACKAGES=bos,fmt,cmdliner,unix,compiler-libs.common,camlp5,camlp5.pr_o.link,camlp5.pa_o.link,camlp5.extfun,camlp5.extend,camlp5.pprintf,camlp5.quotations.link,ounit2,pa_ppx.runtime_fat,pa_ppx.testutils,str,pa_ppx.deriving_plugins.std,camlp5.extend,pa_llk_compiler.link,camlp5,pa_llk_runtime

standalone-o.opt: standalone.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) $(OCAMLCFLAGS) -package $(O_PACKAGES) -syntax camlp5o -linkpkg -linkall -o $@ $<

standalone-r.opt: standalone.cmx
	$(OCAMLFIND) ocamlopt $(DEBUG) $(OCAMLCFLAGS) -package $(R_PACKAGES) -syntax camlp5o -linkpkg -linkall -o $@ $<

standalone-o.exe: standalone.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) $(OCAMLCFLAGS) -package $(O_PACKAGES) -syntax camlp5o -linkpkg -linkall -o $@ $<

standalone-r.exe: standalone.cmo
	$(OCAMLFIND) ocamlc $(DEBUG) $(OCAMLCFLAGS) -package $(R_PACKAGES) -syntax camlp5o -linkpkg -linkall -o $@ $<

standalone.cmx: standalone.ml
	$(OCAMLFIND) ocamlopt $(DEBUG) $(OCAMLCFLAGS) -package $(O_PACKAGES) -syntax camlp5o -linkpkg -linkall -c $<

standalone.cmo: standalone.ml
	$(OCAMLFIND) ocamlc $(DEBUG) $(OCAMLCFLAGS) -package $(O_PACKAGES) -syntax camlp5o -linkpkg -linkall -c $<


R_TOP_PACKAGES=bos,fmt,unix,compiler-libs.common,camlp5,camlp5.pr_r,camlp5.pa_r,camlp5.extfun,camlp5.extend,camlp5.pprintf,camlp5.quotations,ounit2,pa_ppx.runtime_fat,pa_ppx.testutils,str,pa_ppx.deriving_plugins.std,camlp5.extend,pa_llk_compiler,camlp5,pa_llk_runtime
O_TOP_PACKAGES=bos,fmt,unix,compiler-libs.common,camlp5,camlp5.pr_o,camlp5.pa_o,camlp5.extfun,camlp5.extend,camlp5.pprintf,camlp5.quotations,ounit2,pa_ppx.runtime_fat,pa_ppx.testutils,str,pa_ppx.deriving_plugins.std,camlp5.extend,pa_llk_compiler,camlp5,pa_llk_runtime

tops: camlp5.pa_llk_compiler-r camlp5.pa_llk_compiler-r.opt \
	camlp5.pa_llk_compiler-o camlp5.pa_llk_compiler-o.opt

camlp5.pa_llk_compiler-r:
	$(MKCAMLP5) -verbose -package $(R_TOP_PACKAGES) -o $@

camlp5.pa_llk_compiler-r.opt:
	$(MKCAMLP5).opt -verbose -package $(R_TOP_PACKAGES) -o $@

camlp5.pa_llk_compiler-o:
	$(MKCAMLP5) -verbose -package $(O_TOP_PACKAGES) -o $@

camlp5.pa_llk_compiler-o.opt:
	$(MKCAMLP5).opt -verbose -package $(O_TOP_PACKAGES) -o $@

.PRECIOUS: *.opt *.exe *.cmo

clean::
	rm -rf *.cm* *.ppo* *.exe _build camlp5.pa_llk_* *.opt

depend::
	$(OCAMLFIND) ocamldep -package $(PACKAGES),camlp5.macro -syntax camlp5o $(OML) >> .depend.NEW
	$(OCAMLFIND) ocamldep -package $(PACKAGES),camlp5.macro -syntax camlp5r $(RML) >> .depend.NEW
	mv .depend.NEW .depend

-include .depend
