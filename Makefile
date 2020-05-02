all: tests

tests: dotfiles
	for i in tests/*.dot; do dot -Tpdf -o $$i.pdf $$i; done

dotfiles:
	mkdir -p tests
	ocaml tests.ml

pdf: Rapport.tex
	pdflatex $<
	pdflatex $<
	make cleanlatex

cleantests:
	rm -rf *.dot *.dot.pdf tests

cleanlatex:
	rm -f *.aux *.fdb_latexmk *.fls *.log *.out *.synctex.gz *.toc

clean: cleantests cleanlatex
