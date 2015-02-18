set datafile separator ","
set terminal png
set yrange [0:*]
set xrange [0:*]
width = 5
set boxwidth width
rounded(x) = width * floor (x / width)
plot data every ::1 using (rounded(($6+$4+0.01)/($2+0.01))):(1.0) smooth frequency with boxes
