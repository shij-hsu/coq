all:*.v
	coqc -R ~/cpdt/src Cpdt *.v
pdf:*.v
	coqc -R ~/cpdt/src Cpdt *.v
	coqdoc --latex -s *.v 
	pdflatex *.tex
	evince *.pdf
clean:
	rm -rf *.sty *.aux *.glob *.log *.out *.tex *.vo *~
