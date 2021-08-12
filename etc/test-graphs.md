# HoG DB exports

## Files

There are many graphs on 30 vertices, they are split into multiple files:
* regular,
* non-regular, with index < 5.87,
* non-regular, with index >= 5.87,

## Number of vertices less than or equal to 8

* 983 graphs

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

## `IheA@GUAo` (Petersen)

73 (`I`) gives the size of the graph, 10. Adjacency matrix: `104, 101, 65, 64, 71, 85, 65, 111`, with subtracted 63:
`41, 38, 2, 1, 8, 22, 2, 48`

`101001 100110 000010 000001 001000 010110 000010 110000` (last 3 zeroes padded)

```
  0 1 2 3 4 5 6 7 8 9
0 . 1 0 0 1 1 0 0 0 0
1   . 1 0 0 0 1 0 0 0
2     . 1 0 0 0 1 0 0
3       . 1 0 0 0 1 0
4         . 0 0 0 0 1
5           . 0 1 1 0
6             . 0 1 1
7               . 0 1
8                 . 0
9                   .
```
