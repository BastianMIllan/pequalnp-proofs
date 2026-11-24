import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3000 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) → ∀ (x7 : Finset (Fin x2)), x7.card ≤ x1 → ∀ x9 ∉ x7, ∃ (x11 : Fin x2), x3 x11 x9 ∧ ∀ x12 ∈ x7, ¬x3 x11 x12 := by
  intro q N I _ hcard huniq S hS l hl
  by_contra hcon
  push_neg at hcon
  have hA : (Finset.univ.filter (fun p => I p l)).card = q + 1 := by
    rw [← Fintype.card_subtype]; exact hcard l
  have hsub : Finset.univ.filter (fun p => I p l) ⊆
      S.biUnion (fun m => Finset.univ.filter (fun p => I p l ∧ I p m)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨m, hm, hpm⟩ := hcon p hp
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨m, hm, hp, hpm⟩
  have hone : ∀ m ∈ S, (Finset.univ.filter (fun p => I p l ∧ I p m)).card ≤ 1 := by
    intro m hm
    have hml : m ≠ l := fun h => hl (h ▸ hm)
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hab
    obtain ⟨z, _, hu⟩ := huniq a b hab
    have h1 := hu l ⟨ha.1, hb.1⟩
    have h2 := hu m ⟨ha.2, hb.2⟩
    exact hml (h2.trans h1.symm)
  have hle := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hsum : ∑ m ∈ S, (Finset.univ.filter (fun p => I p l ∧ I p m)).card ≤ ∑ _m ∈ S, 1 :=
    Finset.sum_le_sum hone
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
  omega
