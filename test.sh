#!/bin/bash

t=$(date "+%y-%m-%d-%H-%M")
touch "test_log_$t"
for i in {1..170}
do
	echo $i
	# make clean
	make convert LIMIT=1 SKIP=$(($i * 100))
	# cat /home/jure/OneDrive/faks/lean/Lean-HoG/src/hog/data/hog.csv >> "test_log_$t"
	/usr/bin/time -o "test_log_$t" -a lean --make --memory=25000 src/hog/data
	num=$(printf "%05d" $(( $i * 100 + 1)))
	stat --printf="olean size: %s\n" "/home/jure/OneDrive/faks/lean/Lean-HoG/src/hog/data/hog_$num.olean" >> "test_log_$t"
	echo "" >> "test_log_$t"
	# stat --printf="Edge size: %s\n" /home/jure/OneDrive/faks/lean/Lean-HoG/src/hog/data/hog_edge_size_00001.olean >> "test_log_$t"
done
