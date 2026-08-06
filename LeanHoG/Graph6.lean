import LeanHoG.Graph
import LeanHoG.JsonData

/-!
# The graph6 encoding

graph6, from nauty, encodes an undirected simple graph as a string of printable
ASCII:

```
[>>graph6<<] N(n) R(x)
```

Every byte lies in `'?' .. '~'` (63 .. 126) and carries the six-bit value
`byte - 63`.

`N(n)` is the vertex count: one byte `n + 63` when `n ≤ 62`; `'~'` followed by
`n` as 18 bits in three bytes when `63 ≤ n ≤ 258047`; `'~~'` followed by `n` as
36 bits in six bytes above that.

`R(x)` is the upper triangle of the adjacency matrix as a bit vector in
column-major order,

```
a(0,1), a(0,2), a(1,2), a(0,3), a(1,3), a(2,3), a(0,4), …
```

right-padded with zeros to a multiple of six, each six-bit group emitted as its
value plus 63. The bit for the edge `i < j` therefore sits at index
`j*(j-1)/2 + i`, and reading those bits with `i` in the outer loop visits the
edges in lexicographic order.

This module handles graph6. sparse6, the `:`-prefixed format, is a separate
encoding.
-/

namespace LeanHoG

namespace Graph6

/-- The header nauty optionally writes ahead of a graph6 string. -/
def header : String := ">>graph6<<"

/-- Turn a graph6 string into its six-bit values, rejecting bytes outside the
    printable range. -/
def toBytes (s : String) : Except String (Array Nat) := do
  let mut bytes : Array Nat := #[]
  for c in s.toList do
    let n := c.toNat
    if 63 ≤ n && n ≤ 126 then
      bytes := bytes.push (n - 63)
    else
      throw s!"graph6: character {repr c} at position {bytes.size} is outside the printable range '?'..'~'"
  return bytes

/-- Read `k` consecutive six-bit groups starting at `start` as one big-endian number. -/
def readBase64 (bytes : Array Nat) (start k : Nat) : Except String Nat :=
  if start + k ≤ bytes.size then
    .ok <| (List.range k).foldl (fun acc i => (acc <<< 6) ||| bytes.getD (start + i) 0) 0
  else
    throw s!"graph6: the vertex count needs {k} bytes from position {start}, but the string has only {bytes.size}"

/-- Emit `v` as `k` six-bit groups, most significant first. -/
def writeBase64 (k v : Nat) : String :=
  String.ofList <| (List.range k).map fun i =>
    Char.ofNat (((v >>> (6 * (k - 1 - i))) % 64) + 63)

/-- Read `N(n)`: the vertex count, and how many bytes it occupied. -/
def decodeVertexCount (bytes : Array Nat) : Except String (Nat × Nat) := do
  match bytes[0]? with
  | none => throw "graph6: the string is empty"
  | some b0 =>
    if b0 ≤ 62 then
      return (b0, 1)
    -- `b0 = 63`, the byte '~': a wide vertex count follows
    else if bytes.getD 1 0 ≤ 62 then
      return (← readBase64 bytes 1 3, 4)
    else
      return (← readBase64 bytes 2 6, 8)

/-- Write `N(n)`. -/
def encodeVertexCount (n : Nat) : String :=
  if n ≤ 62 then
    String.singleton (Char.ofNat (n + 63))
  else if n ≤ 258047 then
    "~" ++ writeBase64 3 n
  else
    "~~" ++ writeBase64 6 n

/-- The number of bytes `R(x)` occupies for a graph on `n` vertices: one per
    six bits of the upper triangle, rounded up. -/
def payloadSize (n : Nat) : Nat := (n * (n - 1) / 2 + 5) / 6

/-- The bit for the edge `i < j` within `R(x)`. -/
def bitIndex (i j : Nat) : Nat := j * (j - 1) / 2 + i

/-- Bit `k` of `R(x)`, counting from the most significant bit of the first byte. -/
def bit (payload : Array Nat) (k : Nat) : Bool :=
  ((payload.getD (k / 6) 0 >>> (5 - k % 6)) &&& 1) == 1

/-- Decode a graph6 string. The header is optional and surrounding whitespace
    is ignored. -/
def decode (s : String) : Except String GraphData := do
  let s := s.trimAscii.toString
  let s := if s.startsWith header then
      String.ofList (s.toList.drop header.length) |>.trimAscii.toString
    else s
  let bytes ← toBytes s
  let (n, used) ← decodeVertexCount bytes
  let payload := bytes.extract used bytes.size
  let expected := payloadSize n
  if payload.size ≠ expected then
    throw s!"graph6: a graph on {n} vertices needs {expected} bytes of adjacency data, but {payload.size} follow the vertex count"
  let mut edges : Array (Nat × Nat) := #[]
  for i in [0:n] do
    for j in [i+1:n] do
      if bit payload (bitIndex i j) then
        edges := edges.push (i, j)
  return { vertexSize := n, edges := edges }

/-- Encode a graph given as `GraphData`. Inverse of `decode`. -/
def encodeData (D : GraphData) : String :=
  let n := D.vertexSize
  let bits : Array Bool := Id.run do
    let mut bits := Array.replicate (n * (n - 1) / 2) false
    for (a, b) in D.edges do
      let i := min a b
      let j := max a b
      if i < j && j < n then
        bits := bits.set! (bitIndex i j) true
    return bits
  let payload := String.ofList <| (List.range (payloadSize n)).map fun b =>
    Char.ofNat <| 63 + (List.range 6).foldl
      (fun acc k => acc * 2 + (if bits.getD (6 * b + k) false then 1 else 0)) 0
  encodeVertexCount n ++ payload

end Graph6

/-- The graph6 encoding of `G` under its own vertex labelling. -/
def Graph.toGraph6 (G : Graph) : String :=
  Graph6.encodeData
    { vertexSize := G.vertexSize
      edges := G.edgeSet.foldl (fun acc e => acc.push (e.fst.val, e.snd.val)) #[] }

end LeanHoG
