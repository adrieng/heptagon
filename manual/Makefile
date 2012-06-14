# -*- Makefile -*-
# LaTeX Makefile for dvi, ps, and pdf file creation.
# By Jeffrey Humpherys
# Written April 05, 2004
# Revised January 13, 2005
# Revised 2006
# Thanks Bjorn and Boris


LATEX=latex -src-specials
BIBTEX=bibtex
PDFLATEX=pdflatex
DVIPS=dvips -sPAPERSIZE=a4
PS2PDF=ps2pdf -sPAPERSIZE=a4

INTERMEDIATE_FILES=aux,log,bbl,blg,dvi,toc,lof,log,lot,out,cb,nav,snm,vrb

MAIN            = $(shell grep -l documentclass ./*.tex)
SOURCES         = $(wildcard ./*.tex)
FIGURES		= $(wildcard ./figures/*.fig)
ANIMS		= $(wildcard ./anim/*.anim)
TEXANIMS	= $(patsubst %.anim,%.tex,$(ANIMS))
EPSFIGURES      = $(patsubst %.fig,%.eps,$(FIGURES))
PDFFIGURES      = $(patsubst %.fig,%.pdf,$(FIGURES))

PSORPDF=pdf

-include config

DVIS = $(patsubst %.tex,%.dvi,$(MAIN))
PDFS = $(patsubst %.tex,%.pdf,$(MAIN))
PSS  = $(patsubst %.tex,%.ps,$(MAIN))

ifeq ($(PSORPDF),pdf)
	PSORPDFFIGURES=$(PDFFIGURES)
else
	PSORPDFFIGURES=$(EPSFIGURES)
endif

ifeq ($(PSORPDF),pdf)
all: pdf
else
all: dvi
endif

dvi: $(DVIS)
pdf: $(PDFS)
ps: $(PSS)

figures: $(PSORPDFFIGURES)

anim: $(TEXANIMS)

%.dvi: %.tex $(SOURCES) $(EPSFIGURES) $(TEXANIMS)
	$(LATEX) $*
	@while ( grep "Rerun to get cross-references"		\
			$*.log > /dev/null ); do		\
		echo '** Re-running LaTeX **';			\
		$(LATEX) $*;					\
	done

ifeq ($(PSORPDF),pdf)
$(PDFS) : $(SOURCES) $(PDFFIGURES) $(TEXANIMS)
	$(PDFLATEX) $(patsubst %.pdf,%.tex,$@)
	@if ( grep "\\bibdata" $(patsubst %.pdf,%.aux,$@) > /dev/null ); then 	\
		$(BIBTEX) $(patsubst %.pdf,%,$@);				\
	fi
	@while ( grep "Rerun to get cross-references"			\
			$(patsubst %.pdf,%.log,$@) > /dev/null ); do	\
		echo '** Re-running LaTeX **';				\
		$(PDFLATEX) $(patsubst %.pdf,%.tex,$@);			\
	done
else
%.pdf : %.ps
	$(PS2PDF) $*.ps
endif

%.bbl: %.tex %.aux
	$(BIBTEX) $*

%.aux: %.tex
	$(LATEX) $*

%.ps : %.dvi
	$(DVIPS) $*.dvi -o $*.ps

%.tex : %.anim %.fig
	figanim $<

%.eps %.tex: %.fig
	fig2dev -L pstex $*.fig > $*.eps
	fig2dev -L pstex_t -F -p $* $*.fig > $*.tex

%.tex : %.fig
	fig2dev -L $(PSORPDF)tex_t -F -p $* $*.fig > $*.tex

%.pdf %.tex: %.fig
	fig2dev -L pdftex $*.fig > $*.pdf
	fig2dev -L pdftex_t -F -p $* $*.fig > $*.tex

clean:
	rm -f ./*.aux ./*.log ./*.bbl ./*.blg ./*.dvi ./*.toc ./*.lof ./*.log ./*.lot ./*.out ./*.cb ./*.nav ./*.snm ./*.vrb
	rm -f ./*.tex~

figclean:
	rm -f ./figures/*.{tex,eps,pdf,bak}

animclean:
	rm -f ./anim/*.{tex,eps,pdf,bak}

bigclean: figclean animclean clean
	rm -f $(PDFS) $(PSS)
