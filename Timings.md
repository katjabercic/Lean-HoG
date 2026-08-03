# Performance experimentation

## Summary

We used Lean-HoG to verify the number of connected components on more than
23000 graphs stored in HoG. We excluded 6 graphs with more than 2100 edges
that caused stack-overflows even when verified on their individually.

It should be noted that Lean adds an overhead to both time and memory usage.
Even for a graph with one vertex, the time for verifying its number of connected
components is more than 2 seconds and memory usage is almost 2Gb.

In order to mitigate Lean's starting up time, we ran the computation in batches
of 10 graphs. The graphs were sorted by increasing number of edges and the
batches were verified sequentially. Note that a batch size too large can cause
memory usage that exceeds the 64Gb of the machine we used.

The total computation time was 16h and 51 minutes and the maximum memory usage
was 8.5Gb. However, around 82% of the graphs were verified in half the time.
Those graphs had at most 138 edges and memory usage was limited to 2.3Gb. This
is because few graphs in HoG have many edges and the runtime depends mostly on
the number of edges and the number of vertices.

In practice, we could reduce the runtime by using multiple processes (Lean 4 is
single-threaded), provided enough memory is available.

We found no error in the number of connected components in HoG.

## Running the verification

To measure the performance, one can use the branch `verifyAllGraphs` where all
the code is available. The file `Verify.md` in this branch explains how to
verify supported invariants as well as how to measure performance.
