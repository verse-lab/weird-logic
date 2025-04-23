all: Makefile *.tex 
	rm -f *.pyg
	pdflatex -shell-escape --jobname=notes main
	bibtex notes -min-crossrefs=5
	pdflatex -shell-escape --jobname=notes main
	pdflatex -shell-escape --jobname=notes main

quick: Makefile *.tex
	rm -f *.pyg
	pdflatex -shell-escape --jobname=notes main

notes:
	pdflatex -shell-escape --jobname=notes "\def\extflag{}\input{notes}"
	bibtex notes -min-crossrefs=5
	pdflatex -shell-escape --jobname=notes "\def\extflag{}\input{notes}"
	pdflatex -shell-escape --jobname=notes "\def\extflag{}\input{notes}"


clean:
	rm -f *.pyg *.aux *.bbl *.blg *.log *.out *.rel notes*.pdf notes.zip	notes.fdb_latexmk notes.fls notes.pdf

.PHONY: all clean

zip:
	zip notes.zip Makefile *.tex *.bbl mathpartir.sty references.bib frameit.sty llncs.cls fig/*.tex fig/*.pdf tables/*
