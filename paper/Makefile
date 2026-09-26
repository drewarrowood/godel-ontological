# Rebuild the HTML reading copy from main.tex.
# MathJax macros live in html.cfg so a later make4ht run keeps them.

.PHONY: html
html:
	rm -rf .html-build
	mkdir -p .html-build
	cp main.tex refs.bib html.cfg .html-build/
	cd .html-build && pdflatex -interaction=nonstopmode main.tex
	cd .html-build && bibtex main
	cd .html-build && pdflatex -interaction=nonstopmode main.tex
	cd .html-build && pdflatex -interaction=nonstopmode main.tex
	cd .html-build && make4ht -c html.cfg main.tex "xhtml,mathjax,fn-in"
	python3 fix-html.py .html-build/main.html
	cp .html-build/main.html ../docs/index.html
	cp .html-build/main.css ../docs/main.css
	cp .html-build/main*.svg ../docs/
	rm -rf .html-build
