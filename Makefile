OTT_NAME   = lc
SPEC_LOC   = notes
OTT_LOC    = .
COQ_LOC    = coq/lc
AUX_OTT    = 

OTT_SOURCE = $(OTT_NAME)
FILES      = $(OTT_NAME)_ott $(OTT_NAME)_inf
OTTOFLAGS  = -o $(COQ_LOC)/$(OTT_NAME)_ott.v
OTTFILES   = $(foreach i, $(OTT_SOURCE) $(AUX_OTT), $(OTT_LOC)/$(i).ott)
OTTIFLAGS  = $(foreach i, $(OTT_SOURCE) $(AUX_OTT), -i $(OTT_LOC)/$(i).ott) -merge true

all: coq notes

################ latex ####################

SPEC = $(SPEC_LOC)/$(OTT_NAME).mng
SPECFILE = $(SPEC_LOC)/$(OTT_NAME).tex


RULESFILE = $(SPEC_LOC)/$(OTT_NAME)-rules.tex 

notes: 
	(cd $(SPEC_LOC); make)

spec: $(SPEC_LOC)/$(OTT_NAME).pdf

$(SPEC_LOC)/$(OTT_NAME).pdf: $(SPEC) $(SPECFILE)
	ott $(OTTIFLAGS) \
	    -tex_wrap false -tex_show_meta false -tex_filter $(SPEC) $(SPECFILE)
	(cd $(SPEC_LOC); xelatex -interaction nonstopmode $(OTT_NAME).tex)


$(RULESFILE) : $(OTTFILES)
	ott $(OTTIFLAGS) -o $(RULESFILE) \
	          -tex_wrap false \
		  -tex_show_meta false

%.tex: $(RULESFILE) %.mng Makefile
	ott $(OTTIFLAGS) \
            -tex_wrap false \
	    -tex_show_meta false \
	    -tex_filter $*.mng $*.tex

%.pdf : %.tex $(RULESFILE)
	latexmk -bibtex -pdf $*.tex


###################### COQ ##############################

## Paths to executables. Do not include options here.
## Modify these to suit your Coq installation, if necessary.

COQC = coqc
COQDEP = coqdep
COQSPLIT = $(COQ_LOC)/coqsplit

LIBNAME=$(OTT_NAME)
LNGEN=lngen

## Include directories, one per line.

INCDIRS = \
        . \
        $(COQ_LOC) \
        $(METALIBLOCATION) \

## Name of the submakefile generated by coq_makefile
COQMKFILENAME=CoqSrc.mk

VFILES   = $(foreach i, $(FILES), $(COQ_LOC)/$(i).v)
VOFILES  = $(foreach i, $(FILES), $(COQ_LOC)/$(i).vo)
INCFLAGS = $(foreach i, $(INCDIRS), -I $(i))

# Files with exercises to split
SPLIT    = relations
FULL     = $(foreach i, $(SPLIT), $(COQ_LOC)/$(i)_full.v)
SOL      = $(foreach i, $(SPLIT), $(COQ_LOC)/$(i)_sol.v)

.SECONDARY: $(VFILES)

METALIBFILES= $(METALIBLOCATION)/*.v  $(METALIBLOCATION)/Makefile  $(METALIBLOCATION)/README.txt

quick:  $(COQMKFILENAME)
	@$(MAKE) -f $(COQ_LOC)/CoqSrc.mk quick


gen: $(COQ_LOC)/$(OTT_NAME)_ott.v $(COQ_LOC)/$(OTT_NAME)_inf.v $(FULL) $(SOL)

coq: $(COQ_LOC)/$(COQMKFILENAME) $(VFILES)  
	echo "Compiling Coq files"
	cd $(COQ_LOC); $(MAKE) -f CoqSrc.mk

$(COQ_LOC)/%.vo: $(COQ_LOC)/%.v
	cd $(COQ_LOC); $(MAKE) -f CoqSrc.mk $*.vo


$(COQ_LOC)/%_ott.v: $(OTT_LOC)/%.ott 
	ott -i $(OTT_LOC)/$(OTT_NAME).ott $(OTTOFLAGS) -coq_lngen true -coq_expand_list_types true

$(COQ_LOC)/%_inf.v: $(OTT_LOC)/%.ott  
	$(LNGEN) --coq-no-proofs --coq $(COQ_LOC)/$*_inf.v --coq-ott $*_ott $(OTT_LOC)/$*.ott 

$(COQ_LOC)/%_inf_proofs.v: $(OTT_LOC)/%.ott Makefile
	$(LNGEN) --coq $(COQ_LOC)/$*_inf_proofs.v --coq-ott $*_ott $(OTT_LOC)/$*.ott 


$(COQ_LOC)/$(COQMKFILENAME): Makefile $(shell ls $(COQ_LOC)/*.v | grep -v _ott.v | grep -v _inf.v)
	cd $(COQ_LOC); { echo "-R . $(LIBNAME) " ; ls *.v ; } > _CoqProject && coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o $(COQMKFILENAME)


$(COQSPLIT): $(COQSPLIT).ml
	(cd $(COQ_LOC); ocamlc.opt coqsplit.ml -o coqsplit)

$(COQ_LOC)/%_full.v: $(COQ_LOC)/%.v $(COQSPLIT)
	$(COQSPLIT) < $< > $@

$(COQ_LOC)/%_short.v: $(COQ_LOC)/%.v $(COQSPLIT)
	$(COQSPLIT) -terse < $< > $@

$(COQ_LOC)/%_sol.v: $(COQ_LOC)/%.v $(COQSPLIT)
	$(COQSPLIT) -solutions < $< > $@


coqclean:
	(cd $(COQ_LOC); rm -if *.v.d *.vo *.glob *.v-e *.vok *.vos *.conf *.v-e $(VOFILES) $(COQMKFILENAME))

clean: coqclean
	@rm -f *~
	@rm -f *.log *.aux *.fls *.fdb_latexmk
