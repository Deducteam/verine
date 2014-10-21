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

TESTDIR = test
TESTSMTS = $(wildcard $(TESTDIR)/*.smt2)
TESTDKCS = $(TESTSMTS:.smt2=.dkc)
SMTLIBDIR = smtlib2/QF_UF/eq_diamond
BENCHDIR = bench
# Relative path from SMTLIBDIR to BENCHDIR
# RELDIR = ../../bench
BENCHSMTS = $(wildcard $(BENCHDIR)/*.smt2)
BENCHPRFS = $(BENCHSMTS:.smt2=.proof)
BENCHPROVED = $(wildcard $(BENCHDIR)/*.proof)
BENCHDKTS = $(BENCHPROVED:.proof=.dkt)
VERITTIMEOUT = 1
VERINETIMEOUT = 2

.PHONY: all clean test cleantest bench cleanbench cleanbenchsmt2 cleanbenchproof cleanbenchdk

.PRECIOUS: %.proof %.dk

all: verine logic.dko

%.dko: %.dk
	dkcheck -e $<

%.dkc: %.proof verine
	@./verine $< | dkcheck -stdin || true

%.dkt: %.dk
	dkcheck $< || true

#%dk : ne prend pas en compte logic.dk (voir 4))
%.dk: %.proof verine
	timeout $(VERINETIMEOUT) ./verine $< > $@ || rm -f $@

%.proof: %.smt2
	timeout $(VERITTIMEOUT) veriT --proof-version=1 --proof=$@ $< || true

verine: *.ml *.mli *.mll *.mly
	ocamlbuild verine.native
	mv verine.native verine

clean:
	rm -f verine logic.dko *~ *\#
	ocamlbuild -clean

test: verine logic.dko $(TESTDKCS)

cleantest:
	rm -f $(TESTDIR)/*.dk

bench: verine logic.dko $(BENCHDIR)/.dummy $(BENCHPRFS) $(BENCHDKTS)

$(BENCHDIR)/.dummy:
	for f in $(SMTLIBDIR)/*/*.smt2; do cp $$f $(BENCHDIR); done
	touch $(BENCHDIR)/.dummy

cleanbench: cleanbenchsmt2 cleanbenchproof cleanbenchdk

cleanbenchsmt2:
	rm -f $(BENCHDIR)/*.smt2

cleanbenchproof:
	rm -f $(BENCHDIR)/*.dummy
	rm -f $(BENCHDIR)/*.proof

cleanbenchdk:
	rm -f $(BENCHDIR)/*.dk
