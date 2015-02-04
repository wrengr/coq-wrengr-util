# wren gayle romano <wren@cpan.org>                 ~ 2015.02.04
# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

SYNCURL         = wren@community.haskell.org:~/public_html/coq/relations

RM              = rm -f
RMR             = rm -rf
RM_SUFFIXES     = {vo,glob,vi,g,cmi,cmx,o}

LATEXMK         = latexmk
LATEXMK_FLAGS   = -pdf -g
PAPERDIR        = ./latex
PAPER           = Containers

# N.B., versions 8.2 and 8.3 are very different.
COQ_PATH        = /sw/bin/
# COQ_PATH        = /opt/local/bin/

COQDOC          = $(COQ_PATH)/coqdoc
COQDOC_LIBS     =
COQDOC_CSS      = custom.css
HTMLDIR         = ./docs

GALLINA         = $(COQ_PATH)/gallina
COQDEP          = $(COQ_PATH)/coqdep -c
COQC            = $(COQ_PATH)/coqc
COQC_OPT        = -opt
# BUG: we'd like to add -quality but it's not an OTHERFLAG. Where does it go?
COQC_OTHERFLAGS =
COQC_XML        =
COQC_DEBUG      =
SRCDIR          = ./src
# TODO: actually use $(BUILDDIR)
BUILDDIR        = ./build
# TODO: the test stuff needs to be separated out, since it requires Coq 8.2
COQ_FILES       = \
    Util/Tactics/Core \
    Util/Tactics/ExFalso \
    Util/Tactics/Destroy \
    Util/Tactics/Fequal \
    Util/Tactics/Introv \
    Util/Tactics/Jauto \
    Util/Bool \
    Util/ListSet \
    Util/Multiset \
    Util/Nat \
    Util/Option \
    Util/Sumbool

# TODO: should we add Util.Nat.Irrelevance back in?
# TODO: Util.Containers requires Relations.Core

# BUG: the -R flag doesn't seem to be recursing for me ~w
COQC_SRC        = -R $(SRCDIR) ""
COQC_LIBS       =

# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
COQ_VFILES     = $(foreach i, $(COQ_FILES), $(SRCDIR)/$(i).v)
COQ_VOFILES    = $(foreach i, $(COQ_FILES), $(SRCDIR)/$(i).vo)
COQ_GLOBFILES  = $(foreach i, $(COQ_FILES), $(SRCDIR)/$(i).glob)
COQ_VIFILES    = $(foreach i, $(COQ_FILES), $(SRCDIR)/$(i).vi)
COQ_GFILES     = $(foreach i, $(COQ_FILES), $(SRCDIR)/$(i).g)
COQ_HTMLFILES  = $(foreach i, $(COQ_FILES), $(HTMLDIR)/$(i).html)
COQ_GHTMLFILES = $(foreach i, $(COQ_FILES), $(HTMLDIR)/$(i).g.html)
COQ_TEXFILES   = $(foreach i, $(COQ_FILES), $(PAPERDIR)/coqdoc_$(i).tex)

COQC_INCLUDES  = $(foreach i, $(COQC_LIBS), -I $(i)) $(COQC_SRC)
# N.B. The order of flags is really, stupidly, buggily important
COQC_FLAGS     = -q $(COQC_OPT) $(COQC_INCLUDES) $(COQC_OTHERFLAGS) $(COQC_XML)

.SUFFIXES:
.SUFFIXES: .tex .vo .glob .vi .g .html .g.html .pdf
.PHONY: all spec gallina compile extract docs html gallinahtml paper sync clean
# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

all:
	@make compile
	@make docs
	@#make paper

# ~~~~~ 
spec: $(COQ_VIFILES)

%.vi: %.v
	$(COQC) -i $(COQC_DEBUG) $(COQ_FLAGS) $*

# ~~~~~ 
gallina: $(COQ_GFILES)

%.g: %.v
	$(GALLINA) $<


# ~~~~~ Compile the sources
compile: $(SRCDIR)/.depend $(COQ_VOFILES)

extract: $(COQ_VOFILES)
	@echo "Not supported yet"

$(SRCDIR)/.depend : $(COQ_VFILES)
	$(COQDEP) -glob $(COQC_INCLUDES) $(COQ_VFILES) > $(SRCDIR)/.depend 2>/dev/null

include $(SRCDIR)/.depend

%.vo %.glob: %.v
	$(COQC) -dump-glob $*.glob $(COQC_DEBUG) $(COQC_FLAGS) $*.v

	
# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# ~~~~~ Generate html documentation
docs:
	mkdir -p $(HTMLDIR)
	@make html
	@#make gallinahtml

html: $(COQ_HTMLFILES)
	@mkdir -p $(HTMLDIR)
	@# N.B. we need this hack to keep $(SRCDIR) out of the names
	cd $(SRCDIR) ;\
		$(COQDOC) -toc --html --utf8 $(COQDOC_LIBS) -d ../$(HTMLDIR) $(foreach i, $(COQ_FILES), $(i).v)
	if [ -e $(COQDOC_CSS) ] ; then \
		cp -f $(COQDOC_CSS) $(HTMLDIR)/coqdoc.css ; else :; fi

$(HTMLDIR)/%.html: $(SRCDIR)/%.v $(SRCDIR)/%.glob
	@mkdir -p $(HTMLDIR)
	@touch $(HTMLDIR)/coqdoc.css
	$(COQDOC) -glob-from $(SRCDIR)/$*.glob --quiet --noindex --html --utf8 -d $(HTMLDIR) $(SRCDIR)/$*.v -o $(HTMLDIR)/$(subst /,.,$*).html


# ~~~~~ This one doesn't show the proof scripts
# BUG: this doesn't produce hyperlinks correctly...
# BUG: seems like we can't do both "html" and "gallinahtml" targets at once
gallinahtml: $(COQ_GHTMLFILES)
	@mkdir -p $(HTMLDIR)
	@# BUG: why isn't this hack keeping $(SRCDIR) out of the names this time?
	cd $(SRCDIR) ;\
		$(COQDOC) -toc --html --utf8 -g $(COQDOC_LIBS) -d ../$(HTMLDIR) $(foreach i, $(COQ_FILES), $(i).v)
	if [ -e $(COQDOC_CSS) ] ; then \
		cp -f $(COQDOC_CSS) $(HTMLDIR)/coqdoc.css ; else :; fi

$(HTMLDIR)/%.g.html: $(SRCDIR)/%.v $(SRCDIR)/%.glob
	@mkdir -p $(HTMLDIR)
	@touch $(HTMLDIR)/coqdoc.css
	$(COQDOC) -glob-from $(SRCDIR)/$*.glob -g --quiet --noindex --html --utf8 -d $(HTMLDIR) $(SRCDIR)/$*.v -o $(HTMLDIR)/$(subst /,.,$*).g.html


# TODO: a version with -l in lieu of -g, to hide more gunk.


# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# ~~~~~ Typeset the paper
paper: $(COQ_TEXFILES) $(PAPERDIR)/$(PAPER).pdf

%.pdf: %.tex
	cd "`dirname "$*.tex"`" ;\
		$(LATEXMK) $(LATEXMK_FLAGS) "`basename "$*.tex"`"

$(PAPERDIR)/coqdoc_%.tex: $(SRCDIR)/%.v
	$(COQDOC) --short --body-only --latex --utf8 \
		"$(SRCDIR)/$*.v" -o "$(PAPERDIR)/coqdoc_$*.tex"

#all.ps: $(VFILES)
#	$(COQDOC) -toc -ps $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`
#
#all-gal.ps: $(VFILES)
#	$(COQDOC) -toc -ps -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`
#
#all.pdf: $(VFILES)
#	$(COQDOC) -toc -pdf $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`
#
#all-gal.pdf: $(VFILES)
#	$(COQDOC) -toc -pdf -g $(COQDOCLIBS) -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`


# ~~~~~ From Jia et al.'s metatheory Makefile
#DATE = $(shell date +%Y%m%d)
#DIR  = metalib-$(DATE)
#
#COQSPLIT = ../../books/sf/tools/coqsplit
#STLC = ../../books/coqbook/stlc/STLC.v
#
#gens:
#	make -C ../../books/sf tools/coqsplit
#	$(COQSPLIT) < $(STLC) > STLC.v
#	$(COQSPLIT) -solutions < $(STLC) > STLCsol.v
#
#dist:
#	svn export . $(DIR)
#	(cd $(DIR); make docs)
#	$(RM) $(DIR)/*.vo $(DIR)/*.glob
#	$(RM) $(DIR)/TODO.txt
#	echo Release $(DATE) / svn revision `svnversion .` >> $(DIR)/VERSION
#	zip -r $(DIR).zip $(DIR)
#	@echo
#	@echo Done.
#	@echo See $(DIR) and $(DIR).zip.


sync:
	make docs
	mv $(HTMLDIR) $(HTMLDIR).bak
	make clean
	mv $(HTMLDIR).bak $(HTMLDIR)
	rsync -pvrWz --delete --safe-links * $(SYNCURL)

# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
DATE = $(shell date +%Y%m%d)

# ~~~~~ Remove all generated files
clean:
	if [ -d $(PAPERDIR) ] ; then \
		cd $(PAPERDIR) && \
		$(LATEXMK) -C $(PAPER).tex && \
		$(RM) coqdoc_*.tex coqdoc.sty *.bbl ; else :; fi
	@echo ; echo ; echo
	
	@( \
	echo "#!`which sh`" ;\
	echo 'echo '\''$(RM)'\'' "$$1"/'\''*.$(RM_SUFFIXES)'\' ;\
	echo '$(RM) "$$1"/*.$(RM_SUFFIXES)' ;\
	) > make_clean_src-$(DATE).sh
	@#cat make_clean_src-$(DATE).sh | sed 's/^/    /'
	@chmod 755 make_clean_src-$(DATE).sh
	@find $(SRCDIR) -type d -exec ./make_clean_src-$(DATE).sh {} \;
	@$(RM) make_clean_src-$(DATE).sh
	
	$(RM) $(SRCDIR)/.depend
	$(RMR) $(BUILDDIR)
	$(RMR) $(HTMLDIR)


# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ fin.
