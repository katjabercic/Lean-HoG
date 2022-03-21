#!/bin/bash

t=$(date "+%y-%m-%d-%H-%M")
test_log="tests/test_log_$t"
touch $test_log
for i in {1..170}
do
	echo $i
	num=$(printf "%05d" $(( $i * 100 + 1)))
	make convert LIMIT=1 SKIP=$(($i * 100))
	echo $num >> $test_log
	/usr/bin/time -o $test_log -a lean --make --memory=25000 src/hog/data
	/home/jure/Documents/process_io/bin/proccess_io "lean --make --memory=25000 src/hog/data" >> $test_log
	stat --printf="olean size: %s\n" "/home/jure/OneDrive/faks/lean/Lean-HoG/src/hog/data/hog_$num.olean" >> $test_log
	echo "" >> $test_log
done
