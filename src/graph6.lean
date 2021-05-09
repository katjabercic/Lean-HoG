-- Implementation of the graph6 format
-- https://users.cecs.anu.edu.au/~bdm/data/formats.txt

-- decode a string to a list of numbers, all in the range 0 to 63
def decode (s : string) :=
  let lst :=
    list.reverse $
    string.fold []
      (λ lst c, (min 63 (char.to_nat c - 63)) :: lst)
      s
  in
  lst

-- split a list of integers into the graph size and the list encoding
-- the adjancency matrix
def split (lst : list ℕ) :=
  match lst with
  | [] := (0, [])
  | 63 :: a :: b :: c :: d :: lst :=
      let n := ((a * 64 + b) * 64 + c) * 64 + d in
      (n, lst)
  | n :: lst := (n, lst)
  end

def pad6 : list bool → list bool
| [] := [ff, ff, ff, ff, ff, ff]
| [b0] := [ff, ff, ff, ff, ff, b0]
| [b1, b0] := [ff, ff, ff, ff, b1, b0]
| [b2, b1, b0] := [ff, ff, ff, b2, b1, b0]
| [b3, b2, b1, b0] := [ff, ff, b3, b2, b1, b0]
| [b4, b3, b2, b1, b0] := [ff, b4, b3, b2, b1, b0]
| (b5 :: b4 :: b3 :: b2 :: b1 :: b0 :: _) := [b5, b4, b3, b2, b1, b0]

def bits6 (lst : list ℕ) :=
  list.join $
  list.map (λ n , pad6 (nat.bits n)) lst

-- not finished, it just computes the size and the bit list
-- representing the adjancy matrix (upper triangle)
def decode_graph6 (s : string) :=
  let (n, lst) := split (decode s) in
  let adj := bits6 lst in
    (n, adj)

-- examples
#eval decode_graph6 "?"
#eval decode_graph6 "DgC"
#eval decode_graph6 "IheA@GUAo"
