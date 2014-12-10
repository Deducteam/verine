#!/bin/bash
echo "smt2 file,veriT user time,veriT exit status" > $1/veriT_checked
echo "smt2 file,veriT user time,veriT exit status,verine user time,verine exit status" > $1/veriT+verine_checked
echo "smt2 file,veriT user time,veriT exit status,verine user time,verine exit status,dkcheck user time,dkcheck exit status" > $1/veriT+verine+dkcheck_checked
grep ",0$" $1/veriT >> $1/veriT_checked
while read line; do 
	SMTFILE=`echo $line | cut -d "," -f 1`
	echo `grep "$SMTFILE" $1/veriT_checked`","`echo $line | cut -d "," -f 2-` >> $1/veriT+verine
done < $1/verine
grep ",0$" $1/veriT+verine >> $1/veriT+verine_checked
while read line; do 
	SMTFILE=`echo $line | cut -d "," -f 1`
	echo `grep "$SMTFILE" $1/veriT+verine_checked`","`echo $line | cut -d "," -f 2-` >> $1/veriT+verine+dkcheck
done < $1/dkcheck
grep ",0$" $1/veriT+verine+dkcheck >> $1/veriT+verine+dkcheck_checked
rm $1/verine $1/dkcheck
TESTED=`grep ".smt2" $1/veriT | wc -l`
PROVED=`grep ".smt2" $1/veriT_checked | wc -l`
TRANSLATION_TIMEOUT=`grep ",124$" $1/veriT+verine | wc -l`
TRANSLATED=`grep ".smt2" $1/veriT+verine_checked | wc -l`
TRANSLATION_FAILURE=$((PROVED - TRANSLATED - TRANSLATION_TIMEOUT))
CHECKING_TIMEOUT=`grep ",124$" $1/veriT+verine+dkcheck | wc -l`
CHECKED=`grep ".smt2" $1/veriT+verine+dkcheck_checked | wc -l`
CHECKING_FAILURE=$((TRANSLATED - CHECKED - CHECKING_TIMEOUT))
echo "number of tested .smt2 files: "$TESTED >> $1/global
echo "number of proved .smt2 files: "$PROVED >> $1/global
echo "number of translation failures before timout: "$TRANSLATION_FAILURE >> $1/global
echo "number of translated .proof files: "$TRANSLATED >> $1/global
echo "number of checking failures before timout: "$CHECKING_FAILURE >> $1/global
echo "number of checked .dk files: "$CHECKED >> $1/global
echo "proportion of translation failures before timout: "$((TRANSLATION_FAILURE * 100 / PROVED))"%" >> $1/global
echo "proportion of translated .proof files: "$((TRANSLATED * 100 / PROVED))"%" >> $1/global
echo "propertion of checking failures before timout: "$((CHECKING_FAILURE * 100 / TRANSLATED))"%" >> $1/global
echo "proportion of checked .dk files: "$((CHECKED * 100 / TRANSLATED))"%" >> $1/global
gnuplot -p -e "data='$1/veriT+verine+dkcheck_checked'" $2/plot.gp . > $1/speed_stats.png
