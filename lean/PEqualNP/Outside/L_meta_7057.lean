import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7057 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [x3 : DecidableRel x2], (∀ (x4 x5 : Fin x1), x4 ≠ x5 → ∃! x7 : Fin x1, x2 x4 x7 ∧ x2 x5 x7) → ∀ (x5 : Fin x1) (x6 : Finset (Fin x1)), x5 ∉ x6 → Fintype.card { x8 : Fin x1 // x2 x8 x5 ∧ ∃ x9 ∈ x6, x2 x8 x9 } ≤ x6.card := by
  intro x1 x3 x4 h2 l S hl
  rw [Fintype.card_subtype]
  have hsub : (Finset.univ.filter (fun p => x3 p l ∧ ∃ m ∈ S, x3 p m)) ⊆ S.biUnion (fun m => Finset.univ.filter (fun p => x3 p l ∧ x3 p m)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hpl, m, hm, hpm⟩ := hp
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨m, hm, hpl, hpm⟩
  have hone : ∀ m ∈ S, (Finset.univ.filter (fun p => x3 p l ∧ x3 p m)).card ≤ 1 := by
    intro m hm
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hab
    obtain ⟨n, -, hu⟩ := h2 a b hab
    have e1 := hu l ⟨ha.1, hb.1⟩
    have e2 := hu m ⟨ha.2, hb.2⟩
    exact hl (by rw [e1, ← e2]; exact hm)
  have h3 := Finset.card_le_card hsub
  have h4 := Finset.card_biUnion_le (s := S) (t := fun m => Finset.univ.filter (fun p => x3 p l ∧ x3 p m))
  have h5 := Finset.sum_le_card_nsmul S _ 1 hone
  simp only [smul_eq_mul, mul_one] at h5
  omega
