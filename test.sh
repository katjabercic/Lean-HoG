#!/bin/bash

t=$(date "+%y-%m-%d-%H-%M")
for i in {1..170}
do
	echo $i
	make clean
	make convert LIMIT=1 SKIP=$(($i * 100))
	cat /home/jure/OneDrive/faks/lean/Lean-HoG/src/hog/data/hog.csv >> "test_log_$t"
	/home/jure/Documents/process_io/bin/proccess_io "lean --make --memory=25000 src/hog/data" >> "test_log_$t"
	stat --printf="Graph size: %s\n" "/home/jure/OneDrive/faks/lean/Lean-HoG/src/hog/data/hog_graph_00001.olean" >> "test_log_$t"
	stat --printf="Edge size: %s\n" /home/jure/OneDrive/faks/lean/Lean-HoG/src/hog/data/hog_edge_size_00001.olean >> "test_log_$t"
done
