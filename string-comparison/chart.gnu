set style data lines
set datafile separator comma
set datafile columnheaders

set key autotitle columnheader
set title "string construction from string slice (non-borrowing)"
set ylabel "time (nanoseconds)"
set xlabel "string length (bytes)"
set key outside right top vertical box
set logscale x 2

set output "chart.png"
set terminal pngcairo size 1200,800 noenhanced font "Liberation Sans,14" linewidth 1.5

plot for [i=2:*] 'data.csv' using 1:i with linespoints

set output "chart.svg"
set terminal svg size 1200,800 noenhanced font "Arial,Helvetica,14" linewidth 1.5 background rgb "white"
replot