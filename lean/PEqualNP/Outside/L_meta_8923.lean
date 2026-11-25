import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8923

open PEqualNP.HeptadCover

theorem rowcard : ∀ a : Fin 13,
    (Finset.univ.filter fun l : Fin 13 => a ∈ singerLines3 l).card = 4 := by
  decide

theorem colcard : ∀ b : Fin 13, (singerLines3 b).card = 4 := by
  decide

set_option maxRecDepth 100000 in
theorem common : ∀ a1 a2 : Fin 13, a1 ≠ a2 →
    (Finset.univ.filter fun l : Fin 13 => a1 ∈ singerLines3 l ∧ a2 ∈ singerLines3 l).card ≤ 1 := by
  decide

theorem inccard : (incidences singerLines3).card = 52 := by
  decide

theorem rect (A B : Finset (Fin 13)) (h : A ×ˢ B ⊆ incidences singerLines3) :
    5 * (A.card * B.card) ≤ 4 * (A.card + B.card) := by
  have mem : ∀ a ∈ A, ∀ b ∈ B, a ∈ singerLines3 b := by
    intro a ha b hb
    have := h (Finset.mk_mem_product ha hb)
    simpa [incidences] using this
  rcases Nat.lt_or_ge A.card 2 with hA | hA
  · have hA' : A.card = 0 ∨ A.card = 1 := by omega
    rcases hA' with h0 | h1
    · rw [h0]; simp
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
      have hs : B ⊆ Finset.univ.filter fun l => a ∈ singerLines3 l := by
        intro b hb
        simp [mem a (Finset.mem_singleton_self a) b hb]
      have := (Finset.card_le_card hs).trans (rowcard a).le
      simp only [Finset.card_singleton]
      omega
  · rcases Nat.lt_or_ge B.card 2 with hB | hB
    · have hB' : B.card = 0 ∨ B.card = 1 := by omega
      rcases hB' with h0 | h1
      · rw [h0]; simp
      · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp h1
        have hs : A ⊆ singerLines3 b := by
          intro a ha
          exact mem a ha b (Finset.mem_singleton_self b)
        have := (Finset.card_le_card hs).trans (colcard b).le
        simp only [Finset.card_singleton]
        omega
    · exfalso
      obtain ⟨a1, ha1, a2, ha2, hne⟩ := Finset.one_lt_card.mp hA
      obtain ⟨b1, hb1, b2, hb2, hneb⟩ := Finset.one_lt_card.mp hB
      have hc := common a1 a2 hne
      have hs : ({b1, b2} : Finset (Fin 13)) ⊆
          Finset.univ.filter fun l => a1 ∈ singerLines3 l ∧ a2 ∈ singerLines3 l := by
        intro l hl
        rw [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl
        · simp [mem _ ha1 _ hb1, mem _ ha2 _ hb1]
        · simp [mem _ ha1 _ hb2, mem _ ha2 _ hb2]
      have := Finset.card_le_card hs
      rw [Finset.card_pair hneb] at this
      omega

end PEqualNP.Outside.L_meta_8923

open PEqualNP.Outside.L_meta_8923 in
theorem PEqualNP.Outside.L_meta_8923 : ∀ (x1 : Finset (Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)))), (x1.biUnion fun (x2 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))) => x2.1 ×ˢ x2.2) = PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3 → (65 : ℕ) ≤ ∑ x3 ∈ x1, (x3.1.card + x3.2.card) := by
  intro x1 h
  have hsub : ∀ x ∈ x1, x.1 ×ˢ x.2 ⊆ PEqualNP.HeptadCover.incidences
      PEqualNP.HeptadCover.singerLines3 := by
    intro x hx
    rw [← h]
    exact Finset.subset_biUnion_of_mem (fun x2 => x2.1 ×ˢ x2.2) hx
  have hle : 52 ≤ ∑ x ∈ x1, x.1.card * x.2.card := by
    rw [← inccard, ← h]
    refine Finset.card_biUnion_le.trans (le_of_eq ?_)
    exact Finset.sum_congr rfl (fun x _ => Finset.card_product _ _)
  have h2 : 5 * ∑ x ∈ x1, x.1.card * x.2.card ≤ 4 * ∑ x ∈ x1, (x.1.card + x.2.card) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun x hx => rect _ _ (hsub x hx))
  omega
