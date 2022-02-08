
LAUNCH=/home/chet/Hack/Camlp5/src/ALL/camlp5/tools/LAUNCH
OCAMLFIND=$(LAUNCH) ocamlfind
OCAMLC=$(OCAMLFIND) ocamlc -g
PACKAGES=fmt,camlp5,camlp5.extend,camlp5.macro,camlp5.quotations,camlp5.regexp,camlp5.pprintf

all: brz.cmo pa_llk.cmo

brz.cmo: brz.ml
	$(OCAMLFIND) ocamlc -package $(PACKAGES) -c -syntax camlp5o $<

pa_llk.cmo: pa_llk.ml
	$(OCAMLFIND) ocamlc -package $(PACKAGES) -c -syntax camlp5r $<

clean:
	rm -f *.cm* *.o

