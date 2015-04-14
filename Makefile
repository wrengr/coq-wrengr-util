# wren gayle romano <wren@cpan.org>                 ~ 2015.04.14
# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

LIBRARY_NAME    = WrengrUtil
SYNCURL         = wren@community.haskell.org:~/public_html/coq/wrengr-util

RM              = rm -f
RMR             = rm -rf
RM_SUFFIXES     = {vo,glob,vi,g,cmi,cmx,o}

BINDIR          = $(shell dirname $(shell which coqc))
LIBDIR          = $(shell $(BINDIR)/coqtop -where | sed -e 's/\\/\\\\/g')
SRCDIR          = ./src
# TODO: actually use $(BUILDDIR) as intended...
BUILDDIR        = ./build
HTMLDIR         = ./docs

COQDOC          = $(BINDIR)/coqdoc
COQDOC_LIBS     =
COQDOC_CSS      = custom.css

GALLINA         = $(BINDIR)/gallina
COQDEP          = $(BINDIR)/coqdep -c

COQC            = $(BINDIR)/coqc
COQC_OPT        = -opt
# TODO: we'd like to add -quality but it's not an OTHERFLAG. Where
# is it supposed to go exactly?
COQC_OTHERFLAGS =
COQC_XML        =
COQC_DEBUG      =
# N.B., we pass $(LIBRARY_NAME) instead of "" so that the
# compiled/installed libraries are registered under the LIBRARY_NAME
# module namespace; e.g., as WrengrUtil.Tactics.Core instead of as
# just Tactics.Core
COQC_SRC        = -R $(SRCDIR) $(LIBRARY_NAME)
COQC_LIBS       =

MODULES = \
    Tactics/Core \
    Tactics/ExFalso \
    Tactics/Destroy \
    Tactics/Fequal \
    Tactics/Introv \
    Tactics/Jauto \
    CoqExtras/Bool \
    CoqExtras/ListSet \
    CoqExtras/Multiset \
    CoqExtras/Nat \
    CoqExtras/Option \
    CoqExtras/Sumbool \
    CoqExtras/Wf \
    Relations/Core \
    Relations/Temporal \
    Relations/Normalization \
    Relations/ChurchRosser \
    Relations/Properties

# TODO: should we add Util.Container back in?
# TODO: should we add Util.Nat.Irrelevance back in?


# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
MODULES_V     = $(foreach i, $(MODULES), $(SRCDIR)/$(i).v)
MODULES_VO    = $(foreach i, $(MODULES), $(SRCDIR)/$(i).vo)
MODULES_GLOB  = $(foreach i, $(MODULES), $(SRCDIR)/$(i).glob)
MODULES_VI    = $(foreach i, $(MODULES), $(SRCDIR)/$(i).vi)
MODULES_G     = $(foreach i, $(MODULES), $(SRCDIR)/$(i).g)
MODULES_HTML  = $(foreach i, $(MODULES), $(HTMLDIR)/$(i).html)
MODULES_GHTML = $(foreach i, $(MODULES), $(HTMLDIR)/$(i).g.html)

COQC_INCLUDES  = $(foreach i, $(COQC_LIBS), -I $(i)) $(COQC_SRC)
# N.B. The order of flags is really, stupidly, buggily important
COQC_FLAGS     = -q $(COQC_OPT) $(COQC_INCLUDES) $(COQC_OTHERFLAGS) $(COQC_XML)

.SUFFIXES:
.SUFFIXES: .tex .vo .glob .vi .g .html .g.html .pdf
.PHONY: all spec gallina compile extract docs html gallinahtml sync clean
# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

all:
	@make compile
	@make docs

# ~~~~~ 
spec: $(MODULES_VI)

%.vi: %.v
	$(COQC) -i $(COQC_DEBUG) $(COQ_FLAGS) $*

# ~~~~~ 
gallina: $(MODULES_G)

%.g: %.v
	$(GALLINA) $<


# ~~~~~ Compile the sources
compile: $(SRCDIR)/.depend $(MODULES_VO)

extract: $(MODULES_VO)
	@echo "Not supported yet"

$(SRCDIR)/.depend : $(MODULES_V)
	$(COQDEP) -glob $(COQC_INCLUDES) $(MODULES_V) > $(SRCDIR)/.depend 2>/dev/null

include $(SRCDIR)/.depend

%.vo %.glob: %.v
	$(COQC) -dump-glob $*.glob $(COQC_DEBUG) $(COQC_FLAGS) $*.v

	
# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# ~~~~~ Generate html documentation
# BUG: The generated html use unqualified names. How do we get the
# qualified names?

docs:
	mkdir -p $(HTMLDIR)
	@make html
	@#make gallinahtml


# I think this one is the one that generates the files with unqualified
# file names... Maybe it's due to $(MODULES_HTML) being defined
# incorrectly?
html: $(MODULES_HTML)
	@mkdir -p $(HTMLDIR)
	@# N.B. we need this hack to keep $(SRCDIR) out of the names
	cd $(SRCDIR) && \
		$(COQDOC) -toc --html --utf8 $(COQDOC_LIBS) -d ../$(HTMLDIR) $(foreach i, $(MODULES), $(i).v)
	if [ -e $(COQDOC_CSS) ] ; then \
		cp -f $(COQDOC_CSS) $(HTMLDIR)/coqdoc.css ; else :; fi


# BUG: This gives the correct file names, but still shows the
# unqualified names at the top of the page; i.e., in the <h1
# class="libtitle"> tag.
#
# BUG: trying to set the title with the -t or --title flag doesn't
# work; it results in an empty <title> tag.
#
# TODO: should we try using the "-R dir modulespace" flag?
$(HTMLDIR)/%.html: $(SRCDIR)/%.v $(SRCDIR)/%.glob
	@mkdir -p $(HTMLDIR)
	@touch $(HTMLDIR)/coqdoc.css
	$(COQDOC) -glob-from $(SRCDIR)/$*.glob --quiet --noindex --html --utf8 -d $(HTMLDIR) $(SRCDIR)/$*.v -o $(HTMLDIR)/$(LIBRARY_NAME)-$(subst /,-,$*).html


# ~~~~~ This one doesn't show the proof scripts
# BUG: this doesn't produce hyperlinks correctly...
# BUG: seems like we can't do both "html" and "gallinahtml" targets at once
gallinahtml: $(MODULES_GHTML)
	@mkdir -p $(HTMLDIR)
	@# BUG: why isn't this hack keeping $(SRCDIR) out of the names this time?
	cd $(SRCDIR) ;\
		$(COQDOC) -toc --html --utf8 -g $(COQDOC_LIBS) -d ../$(HTMLDIR) $(foreach i, $(MODULES), $(i).v)
	if [ -e $(COQDOC_CSS) ] ; then \
		cp -f $(COQDOC_CSS) $(HTMLDIR)/coqdoc.css ; else :; fi

$(HTMLDIR)/%.g.html: $(SRCDIR)/%.v $(SRCDIR)/%.glob
	@mkdir -p $(HTMLDIR)
	@touch $(HTMLDIR)/coqdoc.css
	$(COQDOC) -glob-from $(SRCDIR)/$*.glob -g --quiet --noindex --html --utf8 -d $(HTMLDIR) $(SRCDIR)/$*.v -o $(HTMLDIR)/$(subst /,.,$*).g.html


# TODO: a version with -l in lieu of -g, to hide more gunk.

# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
# ~~~~~ cf <https://github.com/wouter-swierstra/xmonad/blob/master/Makefile>

# TODO: okay sure, but after doing this, how do we load it?
# HACK: we use a bunch of potentially fragile things to strip $(SRCDIR) and any following "/"s from the front of $i. We should figure out how to make this more robust...
install:
	mkdir -p $(LIBDIR)/user-contrib
	for i in $(MODULES_VO); do \
		j=$${i#"$(SRCDIR)"} ;\
		j="`echo "$$j" | sed 's@^/*@@'`" ;\
		install -d `dirname $(LIBDIR)/user-contrib/$(LIBRARY_NAME)/$$j` ;\
		install $$i $(LIBDIR)/user-contrib/$(LIBRARY_NAME)/$$j ;\
		done


# BUG: this doesn't remove the directories left over from installing...
uninstall:
	@for i in $(MODULES_VO); do \
		j=$${i#"$(SRCDIR)"} ;\
		j="`echo "$$j" | sed 's@^/*@@'`" ;\
		$(RM) $(LIBDIR)/user-contrib/$(LIBRARY_NAME)/$$j ;\
		done


#Makefile.coq: Makefile $(MODULES_V)
#	@coq_makefile -R . $(LIBRARY_NAME) $(MODULES_V) -o Makefile.coq


# ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
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
