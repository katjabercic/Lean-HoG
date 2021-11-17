-- Implementation of the graph6 format
-- https://users.cecs.anu.edu.au/~bdm/data/formats.txt

import tactic
open tactic

-- decode a string to a list of numbers, all in the range 0 to 63
private def string_to_codes (s : string) :=
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

-- pad a list of at most 6 booleans to exactly 6 booleans
private def pad6 : list bool → list bool
| [] := [ff, ff, ff, ff, ff, ff]
| [b0] := [ff, ff, ff, ff, ff, b0]
| [b1, b0] := [ff, ff, ff, ff, b1, b0]
| [b2, b1, b0] := [ff, ff, ff, b2, b1, b0]
| [b3, b2, b1, b0] := [ff, ff, b3, b2, b1, b0]
| [b4, b3, b2, b1, b0] := [ff, b4, b3, b2, b1, b0]
| (b5 :: b4 :: b3 :: b2 :: b1 :: b0 :: _) := [b5, b4, b3, b2, b1, b0]

-- convert a list of numbers to their encodings as hextuples of booleans
private def bits6 (lst : list ℕ) :=
  list.join $
  list.map (λ n , pad6 $ list.reverse $ nat.bits n) lst

-- get the n-th bit in a list
private def get_bit : list bool → ℕ → bool
| [] k := ff
| (b :: _) 0 := b
| (_ :: lst) (k + 1) := get_bit lst k

-- decode the given string as a pair (n, adj) where
-- n is the vertex count of the graph and adj is the
-- adjancency relation encoded by s (symmetrized)
def decode (s : string) : ℕ × (ℕ → ℕ → bool) :=
  let (n, lst) := split (string_to_codes s) in
  let adj := bits6 lst in
  let lookup i j :=
    if i = j then
      ff
    else
      let (i, j) := (min i j, max i j) in
      get_bit adj (nat.div2 (j * nat.pred j) + i)
  in
  (n, lookup)

-- the size of the graph encoded by the given string
def size (s : string) : ℕ := (split (string_to_codes s)).fst

def lookup (s : string) (i j : ℕ) : bool :=
  if i = j then
    ff
  else
    let (i, j) := (min i j, max i j) in
    let (n, lst) := split (string_to_codes s) in
    let adj := bits6 lst in
    get_bit adj (nat.div2 (j * nat.pred j) + i)

-- graph6_lookup is irreflexive
lemma lookup_irreflexive (s : string) :
  irreflexive (λ i j , lookup s i j) :=
  begin
    intro, simp [lookup]
  end

-- the proof that the graph6 decoding results in a symmetric relation
lemma lookup_symmetric (s : string) : 
  symmetric (λ i j , lookup s i j)
  :=
begin
  intros x y p,
  unfold lookup at p ⊢,
  cases (nat.decidable_eq x y),
  {
    rw if_neg at p,
    rw if_neg,
    rw min_comm,
    rw max_comm,
    exact p,
    cc, cc
  },
  { rw if_pos at p,
    rw if_pos,
    exact p,
    cc, cc      
  }
end

-- the Petersen graph
example := decode "IheA@GUAo"