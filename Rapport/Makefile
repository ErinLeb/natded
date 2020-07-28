
SRC=RapportStageL3

pdf:
	pdflatex --shell-escape ${SRC}
	bibtex ${SRC}
	pdflatex --shell-escape ${SRC}
	pdflatex --shell-escape ${SRC}

clean:
	rm -rf *.aux *.log *.out *.bbl *.toc *.blg _minted*
