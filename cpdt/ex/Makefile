all:*.v
	coqc *.v
pdf:*.v
	coqc *.v
	coqdoc --latex -s *.v 
	pdflatex *.tex
	evince *.pdf
clean:
	rm -rf *.sty *.aux *.glob *.log *.out *.tex *.vo *.pdf *~
