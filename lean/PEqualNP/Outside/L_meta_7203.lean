import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7203

open PEqualNP.CircuitLowerBounds

theorem fun_of_nil (n : ℕ) (C : Circuit) (hg : C.gates = []) (x : Fin n → Bool) :
    PEqualNP.MetaComplexity.circuitFun n C x =
      if h : C.output < n then x ⟨C.output, h⟩ else false := by
  unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval Circuit.wires
  rw [hg]
  simp only [List.foldl_nil]
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using h)]

end PEqualNP.Outside.L_meta_7203

theorem PEqualNP.Outside.L_meta_7203 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)),   x5.size = (0 : ℕ) →     (87 : ℕ) ≤ x1 →       x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →         (∀ (x10 : Fin x2), Fintype.card { x11 : Fin x2 // x3 x11 x10 } = x1 + (1 : ℕ)) →           (∀ (x11 x12 : Fin x2), x11 ≠ x12 → ∃! x14 : Fin x2, x3 x11 x14 ∧ x3 x12 x14) →             PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →               (∀ (x13 : Fin (x2 + x2) → Bool), Fintype.card { x14 : Fin x2 // x13 (Fin.natAdd x2 x14) = Bool.true } ≤ x1 → (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.false) →                 let x14 : Fin (x2 + x2) → Fin x2 × Fin x2 → Prop := fun (x14 : Fin (x2 + x2)) (x15 : Fin x2 × Fin x2) => x14 = Fin.castAdd x2 x15.1 ∨ x14 = Fin.natAdd x2 x15.2;                 (∀ x15 ∈ x6, x3 x15.1 x15.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x17 : Fin (x2 + x2)) => Decidable.decide (x14 x17 x15)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x17 : ℕ) => Decidable.decide (x2 ≤ x17)) (↑x15.1) (x2 + ↑x15.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x17 : ℕ) => Decidable.decide (x17 < x2)) (↑x15.1) (x2 + ↑x15.2) = Bool.false) → (∀ x16 ∈ x6, ∀ (x18 : Fin (x2 + x2)), x14 x18 x16 → (24 : ℕ) < (Finset.filter (x14 x18) x6).card) → x6.card ≤ (24 : ℕ) * x5.size := by
  intro x1 x2 x3 x4 x5 x6 hs h87 hx2 _ _ _ hF x14 hx6 _
  have hg : x5.gates = [] := List.length_eq_zero_iff.mp hs
  have hout : ¬ x5.output < x2 + x2 := by
    intro h
    have key := hF (fun i => decide (i.val = x5.output)) ?_ ?_
    · rw [PEqualNP.Outside.L_meta_7203.fun_of_nil _ _ hg, dif_pos h] at key
      simp at key
    · have : Fintype.card { z : Fin x2 // (fun i : Fin (x2 + x2) => decide (i.val = x5.output)) (Fin.natAdd x2 z) = true } ≤ 1 := by
        rw [Fintype.card_le_one_iff_subsingleton]
        constructor
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        simp only [decide_eq_true_eq, Fin.val_natAdd] at ha hb
        exact Subtype.ext (Fin.ext (show a.val = b.val by omega))
      refine le_trans this ?_
      omega
    · rintro ⟨a, b, _, ha, hb⟩
      simp only [decide_eq_true_eq, Fin.val_natAdd, Fin.val_castAdd] at ha hb
      have := a.isLt
      omega
  have hempty : x6 = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    have h2 := (hx6 p hp).2.1
    rw [PEqualNP.Outside.L_meta_7203.fun_of_nil _ _ hg, dif_neg hout] at h2
    exact Bool.false_ne_true h2
  rw [hempty]
  simp
