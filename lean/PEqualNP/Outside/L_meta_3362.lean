import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3362

theorem rect_bound (N : ℕ) (I : Fin N → Fin N → Prop)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N)) (hAB : ∀ p ∈ A, ∀ l ∈ B, I p l) :
    A.card * B.card ≤ A.card + B.card := by
  by_cases hA : A.card ≤ 1
  · calc A.card * B.card ≤ 1 * B.card := Nat.mul_le_mul_right _ hA
      _ ≤ A.card + B.card := by omega
  · push Not at hA
    obtain ⟨p, hp, p', hp', hne⟩ := Finset.one_lt_card.mp hA
    have hB : B.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro l hl l' hl'
      obtain ⟨l0, _, huq⟩ := hu p p' hne
      exact (huq l ⟨hAB p hp l hl, hAB p' hp' l hl⟩).trans
        (huq l' ⟨hAB p hp l' hl', hAB p' hp' l' hl'⟩).symm
    calc A.card * B.card ≤ A.card * 1 := Nat.mul_le_mul_left _ hB
      _ ≤ A.card + B.card := by omega

theorem main (N k m : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hl : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = k)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Fin m → Finset (Fin N))
    (hAB : ∀ i : Fin m, ∀ p ∈ A i, ∀ l ∈ B i, I p l)
    (hcov : ∀ p l : Fin N, I p l → ∃ i : Fin m, p ∈ A i ∧ l ∈ B i) :
    N * k ≤ ∑ i : Fin m, ((A i).card + (B i).card) := by
  set E : Finset (Fin N × Fin N) := Finset.univ.filter (fun x => I x.1 x.2) with hEdef
  have hE : E.card = N * k := by
    rw [hEdef, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
    have h1 : ∀ l : Fin N, (∑ p : Fin N, if I p l then 1 else 0) = k := by
      intro l
      rw [← Finset.card_filter, ← hl l, Fintype.card_subtype]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hsub : E ⊆ Finset.univ.biUnion (fun i => A i ×ˢ B i) := by
    intro x hx
    rw [hEdef, Finset.mem_filter] at hx
    obtain ⟨i, hi1, hi2⟩ := hcov x.1 x.2 hx.2
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ _, Finset.mem_product.mpr ⟨hi1, hi2⟩⟩
  have h2 := Finset.card_le_card hsub
  have h3 := Finset.card_biUnion_le (s := Finset.univ) (t := fun i => A i ×ˢ B i)
  have h4 : ∑ i : Fin m, (A i ×ˢ B i).card ≤ ∑ i : Fin m, ((A i).card + (B i).card) := by
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.card_product]
    exact rect_bound N I hu (A i) (B i) (hAB i)
  omega

end PEqualNP.Outside.L_meta_3362

theorem PEqualNP.Outside.L_meta_3362 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x1 → Fin x1 → Prop) [x5 : DecidableRel x4], (∀ (x6 : Fin x1), Fintype.card { x7 : Fin x1 // x4 x7 x6 } = x2) → (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x4 x7 x10 ∧ x4 x8 x10) → ∀ (x8 x9 : Fin x3 → Finset (Fin x1)), (∀ (x10 : Fin x3), ∀ x11 ∈ x8 x10, ∀ x13 ∈ x9 x10, x4 x11 x13) → (∀ (x11 x12 : Fin x1), x4 x11 x12 → ∃ (x14 : Fin x3), x11 ∈ x8 x14 ∧ x12 ∈ x9 x14) → x1 * x2 ≤ ∑ x12 : Fin x3, ((x8 x12).card + (x9 x12).card) := by
  intro N k m I _ hl hu A B hAB hcov
  exact PEqualNP.Outside.L_meta_3362.main N k m I hl hu A B hAB hcov
