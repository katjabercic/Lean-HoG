#!/bin/bash

t=$(date "+%y-%m-%d-%H-%M")
touch "test_log_$t"
for i in {1..200}
do
	echo $i
	make cleandata
	make convert LIMIT=1 SKIP=$(($i * 100))
	# cat /home/jure/OneDrive/faks/lean/Lean-HoG/src/hog/data/hog.csv >> "test_log_$t"
	num=$(printf "%05d" $((i*100+1)))
	/usr/bin/time -o "test_log_$t" -a /home/jure/Documents/process_io/bin/proccess_io "lean --make --memory=25000 src/hog/data" >> "test_log_$t"
	stat --printf="Graph size: %s\n" "/home/jure/OneDrive/faks/lean/Lean-HoG/src/hog/data/hog_$num.olean" >> "test_log_$t"
	python3 graph_size.py $num $t
done
