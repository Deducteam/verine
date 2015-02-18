# Parameters
VERINEFLAGS =
SMTLIBDIR = smtlib2/QF_UF/SEQ
VERITTIMEOUT = 0.3
VERINETIMEOUT = 3
DKCHECKTIMEOUT = 5

SHELL = /bin/bash
BENCHDIR = bench
STATDIR = stats
BENCHSMTS = $(shell find $(BENCHDIR) -name "*.smt2")
BENCHPRFS_NEEDED = $(BENCHSMTS:.smt2=.proof)
BENCHPRFS = $(shell find $(BENCHDIR) -name "*.proof")
BENCHDKS_NEEDED = $(BENCHPRFS:.proof=.dk)
BENCHDKS = $(shell find $(BENCHDIR) -name "*.dk")
BENCHDKTS_NEEDED = $(BENCHDKS:.dk=.dkt)
STATFILES = $(STATDIR)/$(shell echo -n `date --iso-8601`_smtlibdir_`basename $(SMTLIBDIR)`_veriT_$(VERITTIMEOUT)_verine_$(VERINETIMEOUT)_dkcheck_$(DKCHECKTIMEOUT))

.PHONY: all clean bench cleanbench stats

.PRECIOUS: %.proof %.dk

all: verine logic.dko

%.dko: %.dk
	dkcheck -e $<

%.dkt: %.dk
	/usr/bin/time --quiet -f "$*.smt2,%U,%x" -a -o $(STATFILES)/dkcheck \
		timeout $(DKCHECKTIMEOUT) dkcheck $< \
	|| rm -f $< $*.proof $*.smt2

%.dk: %.proof verine
	/usr/bin/time --quiet -f "$*.smt2,%U,%x" -a -o $(STATFILES)/verine \
		timeout $(VERINETIMEOUT) ./verine $(VERINEFLAGS) $*.smt2 $< > $@ \
	|| rm -f $@ $< $*.smt2

%.proof: %.smt2
	prove_unsat () { timeout $(VERITTIMEOUT) veriT --proof-version=1 --proof=$@ $< \
		&& [[ `cat $@` != 'Formula is Satisfiable' ]]; }; \
	export -f prove_unsat; \
	/usr/bin/time --quiet -f "$<,%U,%x" -a -o $(STATFILES)/veriT bash -c prove_unsat \
	|| rm -f $@ $< 

verine: *.ml *.mli *.mll *.mly
	ocamlbuild -cflags -w,+a -use-ocamlfind -package smt2d verine.native
	mv verine.native verine

clean:
	rm -f verine logic.dko *~ *\#
	ocamlbuild -clean

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
	./stats.sh $(STATFILES)
