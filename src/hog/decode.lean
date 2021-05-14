-- Implementation of the graph6 format
-- https://users.cecs.anu.edu.au/~bdm/data/formats.txt

namespace hog

-- decode a string to a list of numbers, all in the range 0 to 63
private def decode (s : string) :=
  list.reverse $
  string.fold []
    (λ lst c, (min 63 (char.to_nat c - 63)) :: lst)
    s

-- split a list of integers into the graph size and the list encoding
-- the adjancency matrix
private def split : list ℕ → ℕ × list ℕ
| [] := (0, [])
| (63 :: 63 :: a :: b :: c :: d :: e :: f :: lst) :=
    let n := ((((a * 64 + b) * 64 + c) * 64 + d) * 64 + e) * 64 + f in
    (n, lst)
| (63 :: a :: b :: c :: lst) :=
    let n := (a * 64 + b) * 64 + c in
    (n, lst)
| (n :: lst) := (n, lst)

private def pad6 : list bool → list bool
| [] := [ff, ff, ff, ff, ff, ff]
| [b0] := [ff, ff, ff, ff, ff, b0]
| [b1, b0] := [ff, ff, ff, ff, b1, b0]
| [b2, b1, b0] := [ff, ff, ff, b2, b1, b0]
| [b3, b2, b1, b0] := [ff, ff, b3, b2, b1, b0]
| [b4, b3, b2, b1, b0] := [ff, b4, b3, b2, b1, b0]
| (b5 :: b4 :: b3 :: b2 :: b1 :: b0 :: _) := [b5, b4, b3, b2, b1, b0]

private def bits6 (lst : list ℕ) :=
  list.join $
  list.map (λ n , pad6 $ list.reverse $ nat.bits n) lst

private def get_bit : list bool → ℕ → bool
| [] k := ff
| (b :: _) 0 := b
| (_ :: lst) (k + 1) := get_bit lst k

-- not finished, it just computes the size and the bit list
-- representing the adjancy matrix (upper triangle)
def decode_graph6 (s : string) : ℕ × (ℕ → ℕ → bool) :=
  let (n, lst) := split (decode s) in
  let adj := bits6 lst in
  let lookup i j :=
    if i = j then
      ff
    else
      let (i, j) := (min i j, max i j) in
      get_bit adj (nat.div2 (j * nat.pred j) + i)
  in
  (n, lookup)

end hog
