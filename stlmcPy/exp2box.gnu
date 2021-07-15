set terminal pdfcairo mono font "Helvetica, 20" enhanced size 5.8,6.7
set output 'size_new.pdf' 
set datafile missing '-'

## boxplot setting
set style boxplot outliers pointtype 13
set boxwidth 0.5
set pointsize 0.5
set style data boxplot

## custom line style
set style line 1 lt 1 lw 3.3 pt 7 ps 0.4
set style line 2 lt 1 lw 3.5 pt 7 ps 0.4

set title "Size (New)" font ", 55" offset -0.9,-0.4,1

## [1] box1
## [1-1] set y axis
set yrange [50:5000000]
set format y "10^{%T}"
set ytics (600, 5000, 40000, 300000, 1950000) font ", 58" nomirror
set logscale y;

## [1-2] set x axis
set xrange [0.2:5.8]
set xtics nomirror font ", 64" offset -0.9,-0.4,1
set for[i=1:5] xtics add (i 0)
#set grid mxtics xtics ytics
set nogrid
#set xtics scale 0,1

#set ylabel "Size" font ", 60" offset -7.9, 0.5,1 
set lmargin at screen 0.19;
set rmargin at screen 0.97;
set bmargin at screen 0.1;

## box1
plot \
	'./stlmcPy/acc.dat' using (1):1 ls 1 fs solid 0.25 notitle, \
	'' using (2):3 ls 1 fs solid 0.25 notitle, \
	'' using (3):5 ls 1 fs solid 0.25 notitle, \
	'' using (4):7 ls 1 fs solid 0.25 notitle, \
	'' using (5):9 ls 1 fs solid 0.25 notitle

set output 'size_old.pdf'

set title "Size (Old)" font ", 55" offset -0.9,-0.4,1

set yrange [50:5000000]
set format y "10^{%T}"
set ytics (600, 5000, 40000, 300000, 1950000) font ", 58" nomirror
set logscale y;

## [1-2] set x axis
set xrange [0.2:5.8]
set xtics nomirror font ", 64" offset -0.9,-0.4,1
set for[i=1:5] xtics add (i 0)
#set grid mxtics xtics ytics
set nogrid
#set xtics scale 0,1

unset ylabel
## box2
plot \
	'./stlmcPy/acc.dat' using (1):2 ls 2 notitle, \
	'' using (2):4 ls 2 notitle, \
	'' using (3):6 ls 2 notitle, \
	'' using (4):8 ls 2 notitle, \
	'' using (5):10 ls 2 notitle

## unset all settings
unset ytics

## [2] right box
## [2-1] set y axis
set logscale y
set yrange [0.004:1000]
set ytics (0.07, 0.7, 6, 50, 360) font ", 58" nomirror
set format y "10^{%T}"

## [2-2] set x axis
set title "Time (New)" font ", 55" offset -0.9,-0.4,1


#set ylabel "Time" font ", 60" offset -6.9, 0.5,1 
set output 'time_new.pdf'

## box3
plot \
	'./stlmcPy/time.dat' using (1):1 ls 1 fs solid 0.25 notitle, \
	'' using (2):3 ls 1 fs solid 0.25 notitle, \
	'' using (3):5 ls 1 fs solid 0.25 notitle, \
	'' using (4):7 ls 1 fs solid 0.25 notitle, \
	'' using (5):9 ls 1 fs solid 0.25 notitle

set output 'time_old.pdf'
set title "Time (Old)" font ", 55" offset -0.9,-0.4,1
set logscale y
set yrange [0.004:1000]
set ytics (0.07, 0.7, 6, 50, 360) font ", 58" nomirror
set format y "10^{%T}"

## [2-2] set x axis


unset ylabel
set label "T/O:" at graph 0.88,0.9 right font ",57"
set label "{d_4, d_5}" at graph 0.96,0.77 right font ",57"
## box4
plot \
	'./stlmcPy/time.dat' using (1):2 ls 2 notitle, \
	'' using (2):4 ls 2 notitle, \
	'' using (3):6 ls 2 notitle


unset multiplot




