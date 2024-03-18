import Lean
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Order.Basic
import Mathlib.Data.Prod.Lex

namespace LeanHoG

structure Edge (m : Nat) where
  fst : Fin m
  snd : Fin m
  ord : (fst : Nat) < snd
deriving Fintype, Repr

def Edge.fromNats {m : Nat} (i j : Nat) (h₁ : i < j) (h₂ : j < m) : Edge m :=
  {
    fst := ⟨i, lt_trans h₁ h₂⟩,
    snd := ⟨j, h₂⟩,
    ord := h₁
  }

-- smart constructor used to load JSON files
def Edge.mk' (n a b : Nat) (H1 : Nat.blt a b = true) (H2 : Nat.blt b n = true) : Edge n :=
  let H1 := Nat.le_of_ble_eq_true H1
  let H2 := Nat.le_of_ble_eq_true H2
  ⟨⟨a, lt_trans H1 H2⟩, ⟨b, H2⟩, H1⟩

@[simp, reducible]
def fst_snd (m : Nat) (e : Edge m) : Lex (Fin m × Fin m) := (e.fst, e.snd)

def fst_snd_injective {m : Nat} : Function.Injective (fst_snd m) := by
  intro a b
  cases a ; cases b ; simp
  intro h ; injection h ; trivial

instance Edge.linearOrder {m : Nat} : LinearOrder (Edge m) :=
  LinearOrder.lift' (fst_snd m) fst_snd_injective

end LeanHoG
