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
SMTLIBDIR = smtlib2/QF_UFIDL
BENCHDIR = bench
# Relative path from SMTLIBDIR to BENCHDIR
RELDIR = ../../bench
SMTLIBSMTS = $(wildcard $(BENCHDIR)/*.smt2)

.PHONY: all clean test cleantest bench cleanbench

.PRECIOUS: %.proof

all: verine logic.dko

%.dko: %.dk
	dkcheck -e $<

#%dk : ne prend pas en compte logic.dk (voir 4))

# %.dkc: %.proof verine
# 	./verine $<
# 	dkcheck $@ || true

%.dkc: %.proof verine
	@./verine $< | dkcheck -stdin || true

%.proof: %.smt2
		veriT --proof-version=1 --proof=$@ $<

verine: *.ml *.mli *.mll *.mly
	ocamlbuild verine.native
	mv verine.native verine

clean:
	rm -f verine logic.dko *~ *\#
	ocamlbuild -clean

test: verine logic.dko $(TESTDKCS)

cleantest:
	rm -f $(TESTDIR)/*.proof

bench: verine logic.dko $(BENCHDIR)/.dummy

$(BENCHDIR)/.dummy:
	shopt -s nullglob && \
	  cd $(SMTLIBDIR) && for f1 in *.smt2 ; do cp $$f1 $(RELDIR); done && \
	  for d1 in ./*; do if test -d $$d1; then \
	    cd $$d1 && for f2 in *.smt2 ; do cp $$f2 ../$(RELDIR); done && \
	    for d2 in ./*; do if test -d $$d2; then \
	      cd $$d2 && for f3 in *.smt2 ; do cp $$f3 ../../$(RELDIR); done && \
	      for d3 in ./*; do if test -d $$d3; then \
	        cd $$d3 && for f4 in *.smt2 ; do cp $$f4 ../../../$(RELDIR); done && \
	        for d4 in ./*; do if test -d $$d4; then \
	          cd $$d4 && for f5 in *.smt2 ; do cp $$f5 ../../../../$(RELDIR); done && \
	          for d5 in ./*; do if test -d $$d5; then echo "need deeper search"; \
	          fi done && cd ..; \
	        fi done && cd ..; \
	      fi done && cd ..; \
	    fi done && cd ..; \
	  fi done
	touch $(BENCHDIR)/.dummy

cleanbench:
	rm -f $(BENCHDIR)/.dummy
