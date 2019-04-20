PROJNAME=spec

.PHONY: pdf all clean

all: $(PROJNAME).pdf

pdf: report/$(PROJNAME).tex
	cd ./report && latexmk -pdf -pdflatex="pdflatex -interactive=nonstopmode" -use-make $(PROJNAME).tex

cleanall:
	cd ./report && latexmk -C
	rm -rf report/$(PROJNAME).spl
	rm -rf homework2.zip report/$(PROJNAME).bbl

clean:
	cd ./report && latexmk -c
	rm -rf report/$(PROJNAME).spl report/$(PROJNAME).bbl

zippure:
	zip -j homework2.zip report/$(PROJNAME).pdf src/code.dfy

zip: cleanall pdf zippure clean
