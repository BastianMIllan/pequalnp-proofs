import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2992

open PEqualNP.CircuitLowerBounds

-- The empty circuit whose output wire does not exist: it is constantly false.
def emptyC (n : ℕ) : Circuit := ⟨[], n⟩

lemma emptyC_false (n : ℕ) (x : Fin n → Bool) :
    PEqualNP.MetaComplexity.circuitFun n (emptyC n) x = false := by
  unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval Circuit.wires emptyC
  simp only [List.foldl_nil]
  exact List.getD_eq_default _ _ (by simp)

lemma emptyC_AO2 (n : ℕ) : PEqualNP.TopForm.IsAO2 n (emptyC n) := by
  unfold PEqualNP.TopForm.IsAO2 PEqualNP.EdgeOwnership.AndOrOnly
    PEqualNP.MetaComplexity.NestedCover.ReadsBack emptyC
  simp

lemma emptyC_readK (n : ℕ) : PEqualNP.ReadK.IsReadK n (emptyC n) 2 := by
  intro S hS
  exfalso
  have h := hS.1
  rw [emptyC_false] at h
  exact Bool.false_ne_true h

end PEqualNP.Outside.L_meta_2992

theorem PEqualNP.Outside.L_meta_2992 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (201 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x9 ∧ PEqualNP.ReadK.IsReadK (x2 + x2) x9 (2 : ℕ) ∧ x9.size ≤ (2 : ℕ) * x2 := by
  intro x1 x2 x3 _ _ _ _ _
  refine ⟨PEqualNP.Outside.L_meta_2992.emptyC (x2 + x2),
    PEqualNP.Outside.L_meta_2992.emptyC_AO2 _, PEqualNP.Outside.L_meta_2992.emptyC_readK _, ?_⟩
  simp [PEqualNP.Outside.L_meta_2992.emptyC, PEqualNP.CircuitLowerBounds.Circuit.size]
