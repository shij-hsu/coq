pdf:*.v
	coqc -R . pdf *.v
	coqdoc  -R . pdf --interpolate --latex *.v -o autorewrite.tex
	coqdoc  -R . pdf *.v
	pdflatex *.tex
	evince *.pdf
clean:
	rm -rf *.tex *.pdf *.css *.sty *.out *.aux *.dvi *.log *.html *.ind *.ilg
