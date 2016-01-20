

pdf: tex
	pdflatex main.tex

tex:
	pandoc slides.md --slide-level 2 --listings -t beamer -o slides.tex

run:
	ls slides.md main.tex | entr make pdf
