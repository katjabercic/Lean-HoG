import Std.Sat.CNF
import Trestle.Data.ICnf.Basic
import Trestle.Encode.VEncCNF

/-!
Connect Trestle's DIMACS-oriented `ICnf` representation to `Std.Sat.CNF Nat`.

`Std.Tactic.BVDecide.LRAT` checks proofs against `Std.Sat.CNF Nat`, while
Trestle's encoders produce `ICnf`. The conversion uses zero-based variable
indices: Std's LRAT checker shifts its `Nat` variables to one-based DIMACS
identifiers internally.
-/

namespace Trestle

open Model PropFun

namespace ILit

/-- Convert a Trestle DIMACS literal to a Std literal with a zero-based variable. -/
def toStd (l : ILit) : Std.Sat.Literal Nat :=
  (l.index, LitVar.polarity l)

theorem ofIndex_index (l : ILit) :
    IVar.ofIndex l.index = LitVar.toVar l := by
  rw [← ILit.toVar_index, IVar.ofIndex_index]

end ILit

namespace IClause

/-- Convert a Trestle clause to Std's list-based clause representation. -/
def toStd (clause : IClause) : Std.Sat.CNF.Clause Nat :=
  clause.toList.map ILit.toStd

theorem satisfies_toStd_iff (clause : IClause) (τ : Model.PropAssignment IVar) :
    Std.Sat.CNF.Clause.eval (τ ∘ IVar.ofIndex) clause.toStd = true ↔
      τ ⊨ clause.toPropFun := by
  rw [Clause.satisfies_iff]
  constructor
  · intro h
    rw [Std.Sat.CNF.Clause.eval, List.any_eq_true] at h
    obtain ⟨stdLit, hMem, hEval⟩ := h
    rw [toStd, List.mem_map] at hMem
    obtain ⟨lit, hMem, rfl⟩ := hMem
    refine ⟨lit, ?_, ?_⟩
    · exact Array.mem_toList_iff.mp hMem
    · rw [LitVar.satisfies_iff]
      change (τ (IVar.ofIndex lit.index) == LitVar.polarity lit) = true at hEval
      rw [beq_iff_eq, ILit.ofIndex_index] at hEval
      exact hEval
  · rintro ⟨lit, hMem, hEval⟩
    rw [Std.Sat.CNF.Clause.eval, List.any_eq_true]
    refine ⟨lit.toStd, ?_, ?_⟩
    · rw [toStd, List.mem_map]
      exact ⟨lit, Array.mem_toList_iff.mpr hMem, rfl⟩
    · rw [LitVar.satisfies_iff] at hEval
      change (τ (IVar.ofIndex lit.index) == LitVar.polarity lit) = true
      rw [beq_iff_eq, ILit.ofIndex_index]
      exact hEval

end IClause

namespace ICnf

/-- Convert a Trestle CNF to Std's list-based CNF representation. -/
def toStd (cnf : ICnf) : Std.Sat.CNF Nat :=
  cnf.toList.map IClause.toStd

theorem satisfies_toStd_iff (cnf : ICnf) (τ : Model.PropAssignment IVar) :
    Std.Sat.CNF.Sat (τ ∘ IVar.ofIndex) cnf.toStd ↔
      τ ⊨ cnf.toPropFun := by
  simp only [Std.Sat.CNF.sat_def, Std.Sat.CNF.eval, List.all_eq_true, toStd, List.mem_map,
    Cnf.satisfies_iff]
  constructor
  · intro h clause hClause
    exact IClause.satisfies_toStd_iff clause τ |>.mp <|
      h (IClause.toStd clause) ⟨clause, Array.mem_toList_iff.mpr hClause, rfl⟩
  · intro h stdClause hStdClause
    obtain ⟨clause, hClause, rfl⟩ := hStdClause
    exact IClause.satisfies_toStd_iff clause τ |>.mpr <|
      h clause (Array.mem_toList_iff.mp hClause)

/-- The conversion preserves satisfiability. -/
theorem sat_toStd_iff (cnf : ICnf) :
    (∃ τ, Std.Sat.CNF.Sat τ cnf.toStd) ↔ Cnf.Sat cnf := by
  constructor
  · rintro ⟨τ, hτ⟩
    let τ' : Model.PropAssignment IVar := τ ∘ IVar.index
    refine ⟨τ', ?_⟩
    apply (satisfies_toStd_iff cnf τ').mp
    simpa [τ', Function.comp_def] using hτ
  · rintro ⟨τ, hτ⟩
    exact ⟨τ ∘ IVar.ofIndex, (satisfies_toStd_iff cnf τ).mpr hτ⟩

/-- The conversion preserves unsatisfiability. -/
theorem unsat_toStd_iff (cnf : ICnf) :
    cnf.toStd.Unsat ↔ ¬ Cnf.Sat cnf := by
  rw [← sat_toStd_iff]
  simp only [Std.Sat.CNF.Unsat, Std.Sat.CNF.Sat]
  constructor
  · intro h ⟨τ, hτ⟩
    rw [h τ] at hτ
    contradiction
  · intro h τ
    apply Bool.eq_false_iff.mpr
    intro hτ
    exact h ⟨τ, hτ⟩

end ICnf

namespace Encode.VEncCNF

/-- Unsatisfiability of the CNF an encoding emits, as accepted by the LRAT checker, implies
that the property the encoding was proved to express has no satisfying assignment. -/
theorem std_unsat_no_assignment {ν : Type} [IndexType ν] [LawfulIndexType ν] {α : Type _}
    {P : Model.PropPred ν} (e : VEncCNF ν α P) (h : e.val.toICnf.toStd.Unsat) :
    ¬ ∃ τ, P τ := by
  intro hP
  have hICnf : ¬ Cnf.Sat e.val.toICnf := (ICnf.unsat_toStd_iff _).mp h
  exact hICnf ((toICnf_equisatisfiable e).mpr hP)

end Encode.VEncCNF

end Trestle
