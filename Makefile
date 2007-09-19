
#noargs:: usage parts
noargs:: proto

CAMLC=ocamlc -c
CAMLLINK=ocamlc

COQC=$(COQBIN)coqc
COQ=$(COQBIN)coqtop -batch
COQDEP=$(COQBIN)coqdep
COQDOC=$(COQBIN)coqdoc

OPT=-opt
XML=
COQFLAGS=-q
COQOPTS=$(OPT) $(XML) $(COQFLAGS)

DATE=`date +'%h %d %Y %H:%M:%S'`
COQBANNER=`$(COQ) -v | tr '\n' '~'`

MYLIBS=MyList.vo MyRelations.vo General.vo
FILES=Main.vo GenericSort.vo SortECC.vo SortV6.vo CoqV6.vo ECC.vo CoqV6Beta.vo

# Subsections of Main
MODTERMES=Termes.v Env.v Subtyping_rule.v
MODTYPING=PTS_spec.v Metatheory.v Infer.v
MODRULES=Rules.v Normal.v Conv.v Soundness.v
MODCUMUL=CTS_spec.v Cumul.v CumulDec.v CumulInfer.v
MODLAMBDA=Lambda_Rules.v LambdaSound.v Confluence.v BD.v Beta.v
MAINFILES=$(MODTERMES) $(MODTYPING) $(MODRULES) $(MODCUMUL) $(MODLAMBDA)

VERSION=ExtractV6.v
#VERSION=ExtractV6Beta.v
#VERSION=ExtractECC.v

ALLV=$(MYLIBS:.vo=.v) $(MAINFILES) $(FILES:.vo=.v) \
     Atermes.v Atyping.v Arules.v Acumul.v Alambda.v \
     Ltermes.v Ltyping.v Lrules.v Lcumul.v Llambda.v \
     Errors.v MlExtract.v $(VERSION)

ALLHTML=$(ALLV:.v=.html)

usage::
	@echo "targets:"
	@echo "  all: parts + proto"
	@echo "  proto: eccd + test"
	@echo "  test: lemme de Newman"
	@echo "  html: html pages of .v files"
	@echo "  clean: doesn't remove .vo"
	@echo "  cleanall: also removes .vo"

all:: parts proto

proto:: $(MYLIBS) Main.vo $(FILES) eccd test

parts:: Atermes.vo Atyping.vo Arules.vo Acumul.vo Alambda.vo

html:: $(ALLHTML) main.html

test:: eccd
	(cd examples; ./test_def ../eccd)


eccd: kernel.cmo checker.cmo
	$(CAMLLINK) -o eccd kernel.cmo checker.cmo

kernel.ml: $(VERSION) MlExtract.vo Main.vo
	$(COQ) $(COQOPTS) -load-vernac-source $(VERSION)

checker.cmo: kernel.cmo

main.html: main.html.tpl
	rm -f main.html
	@echo Date: $(DATE)
	sed -e "s|COMPILDATE|$(DATE)|" -e "s|COQBANNER|$(COQBANNER)|" \
            -e "s|~|<br>|g" main.html.tpl > $@
	chmod a-w $@


clean::
	rm -f *.vo *.cm* kernel.* eccd *.html

cleanall:: clean
	rm -f *.vo $(ALLHTML)

depend::
	rm -f .depend
	$(COQDEP) -c *.v *.ml *.mli >.depend



.SUFFIXES: .v .vo .ml .mli .cmo .cmi .cmx .html

.v.vo:
	$(COQC) $(COQOPTS) $<
#	$(COQC) $(COQOPTS) -dump-glob $*.l $<

.mli.cmi:
	$(CAMLC) $<

.ml.cmo:
	$(CAMLC) -pp camlp4o $<

.v.html:
	$(COQDOC) --html $< -o $@

include .depend

# Other dependencies
ExtractV6Beta.v: CoqV6Beta.vo
ExtractV6.v: CoqV6.vo
ExtractECC.v: ECC.vo

Atermes.vo: $(MODTERMES)
Atyping.vo: $(MODTYPING)
Arules.vo: $(MODRULES)
Acumul.vo: $(MODCUMUL)
Alambda.vo: $(MODLAMBDA)
Main.vo: $(MAINFILES)

