#Remarques :
#1) Application de la règle x: y
#   Dans tous les cas, le système cherche d'abord à mettre à jour y
#   Différents cas :
#     - x et y existent : appliquée ssi y plus récent que x
#     - x n'existe pas, y existe : toujours appliquée (un fichier inexistant se comporte comme un fichier très ancien)
#     - y n'existe pas, x existe : jamais appliquée (pour la meme raison)
#     - x et y n'existent pas : toujours appliquée
#
#2) Ne pas utiliser .y.x: qui est obselète
#   en particulier parce que .y.x: z est interprété comme ".y.x": z
#
#3) .PHONY : règles lancées même si il existe un fichier à jour correspondant à la cible
#
#4) Fichiers intermédiaires :
#   - par défaut, ensemble des fichiers à la fois créés et utilisés par des règles implicites
#   - par défaut, ils sont supprimés après avoir été utilisés
#   - si une cible dépend d'un fichier intermédiaire qui n'existe pas, ce fichier ne sera créé que s'il existe dans ses dépendances une cible à mettre à jour
#   .INTERMEDIATE déclare des fichiers intermédiaires
#   .SECONDARY déclare des fichiers intermédiaire à ne pas supprimer
#
#Utilisation : 
#  - make
#  - make clean
#  - make test pour créer tous les dks et les vérifier
#  - make fichier.dk pour créer un dk et le vérifier

SHELL = /bin/bash
VERINEFLAGS =
TESTDIR = test
TESTSMTS = $(wildcard $(TESTDIR)/*.smt2)
TESTDKCS = $(TESTSMTS:.smt2=.dkc)
SMTLIBDIR = smtlib2/QF_UF/SEQ
BENCHDIR = bench
BENCHSMTS = $(shell find $(BENCHDIR) -name "*.smt2")
BENCHPRFS_NEEDED = $(BENCHSMTS:.smt2=.proof)
BENCHPRFS = $(shell find $(BENCHDIR) -name "*.proof")
BENCHDKS_NEEDED = $(BENCHPRFS:.proof=.dk)
BENCHDKS = $(shell find $(BENCHDIR) -name "*.dk")
BENCHDKTS_NEEDED = $(BENCHDKS:.dk=.dkt)
VERITTIMEOUT = 0.3
VERINETIMEOUT = 3
DKCHECKTIMEOUT = 5
STATDIR = stats
STATFILES = $(STATDIR)/$(shell echo -n `date --iso-8601`_smtlibdir_`basename $(SMTLIBDIR)`_veriT_$(VERITTIMEOUT)_verine_$(VERINETIMEOUT)_dkcheck_$(DKCHECKTIMEOUT))

.PHONY: all clean test cleantest bench cleanbench stats

.PRECIOUS: %.proof %.dk

all: verine logic.dko

%.dko: %.dk
	dkcheck -e $<

%.dkc: %.proof verine
	@./verine $(VERINEFLAGS) $*.smt2 $< | dkcheck -stdin || true

%.dkt: %.dk
	/usr/bin/time --quiet -f "$*.smt2,%U,%x" -a -o $(STATFILES)/dkcheck \
		timeout $(DKCHECKTIMEOUT) dkcheck $< \
	|| rm -f $< $*.proof $*.smt2

#%dk : ne prend pas en compte logic.dk (voir 4))
%.dk: %.proof verine
	/usr/bin/time --quiet -f "$*.smt2,%U,%x" -a -o $(STATFILES)/verine \
		timeout $(VERINETIMEOUT) ./verine $(VERINEFLAGS) $*.smt2 $< > $@ \
	|| rm -f $@ $< $*.smt2

%.proof: %.smt2
	prove_unsat () { timeout $(VERITTIMEOUT) veriT --proof-version=1 --proof=$@ $< \
		&& [[ `cat $@` != 'Formula is Satisfiable' ]]; }; \
	export -f prove_unsat; \
	/usr/bin/time --quiet -f "$<,%U,%x" -a -o $(STATFILES)/veriT bash -c prove_unsat || rm -f $@ $< 

verine: *.ml *.mli *.mll *.mly
	ocamlbuild -cflags -w,+a -use-ocamlfind -package smt2d verine.native
	mv verine.native verine

clean:
	rm -f verine logic.dko *~ *\#
	ocamlbuild -clean

test: verine logic.dko $(TESTDKCS)

cleantest:
	rm -f $(TESTDIR)/*.dk

bench: verine logic.dko $(BENCHDIR)/.dummy $(BENCHPRFS_NEEDED) $(BENCHDKS_NEEDED) $(BENCHDKTS_NEEDED)

$(BENCHDIR)/.dummy:
	[ -e $(BENCHDIR) ] || mkdir $(BENCHDIR)
	cp -r $(SMTLIBDIR) $(BENCHDIR)
	touch $(BENCHDIR)/.dummy

cleanbench:
	rm -fr bench

stats:
	make cleanbench
	make bench
	rm -rf $(STATFILES)
	mkdir $(STATFILES)
	echo "smt2 file,veriT user time,veriT exit status" > $(STATFILES)/veriT
	echo "smt2 file,verine user time,verine exit status" > $(STATFILES)/verine
	echo "smt2 file,dkcheck user time,dkcheck exit status" > $(STATFILES)/dkcheck
	echo "bench directory: "`basename $(SMTLIBDIR)` > $(STATFILES)/global
	echo "veriT timeout: "$(VERITTIMEOUT) >> $(STATFILES)/global
	echo "verine timeout: "$(VERINETIMEOUT) >> $(STATFILES)/global
	echo "dkcheck timeout: "$(DKCHECKTIMEOUT) >> $(STATFILES)/global
	make bench
	make bench
	make bench
	$(STATDIR)/stats.sh $(STATFILES) $(STATDIR)
