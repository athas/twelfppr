lhss := $(shell find . -name "*.lhs" -print)
date := $(shell date +%Y-%m-%d)
DIST := twelfppr--$(date)

all : twelfppr.pdf

twelfppr.pdf : twelfppr.tex
	pdflatex -halt-on-error -file-line-error $<

twelfppr.tex : $(lhss)
	lhs2TeX --poly TwelfPPR.lhs > $@

tags : $(lhss)
	hasktags -e $^

clean:
	rm -f twelfppr.pdf
	rm -f twelfppr.tex