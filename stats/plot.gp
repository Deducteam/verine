set datafile separator ","
set terminal svg
plot data every ::1 using (($6+$4+0.01)/($2+0.01)) smooth frequency with boxes
