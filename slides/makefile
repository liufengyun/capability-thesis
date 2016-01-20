

pdf:
	pandoc slides.md --slide-level 2 -t beamer -o slides.tex
	pdflatex main.tex

tex:
	pandoc --slide-level 2 -t beamer slides.md -o slides.tex

pdfdirect:
	pandoc --slide-level 2 -t beamer slides.md -o slides.pdf
	# pandoc --toc --slide-level 2 -V theme:Frankfurt -t beamer slides.md -o slides.pdf

run:
	ls slides.md main.tex | entr make pdf
