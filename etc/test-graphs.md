# Work out adjacency matrices by hand

## `DgC` (P_2 U P_3)

```
D: 68 - 63 = 5 => 000101
g: 103 - 63 = 40 => 101000
C: 67 - 63 = 4 => 000100
```

This gives us the bit vector a graph of size 5 with the upper triangle `101000 000100` (last two zeroes are padded):

```
  0 1 2 3 4
0 . 1 0 0 0
1   . 1 0 0
2     . 0 0
3       . 1
4         .
```

This is the graph `0-1-2 3-4`.
