import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8541

theorem through (n q : ℕ) (S : Fin n → Finset (Fin n)) (hq : 0 < q)
    (hn : n = q ^ 2 + q + 1) (hcard : ∀ l : Fin n, (S l).card = q + 1)
    (huniq : ∀ a b : Fin n, a ≠ b → ∃! l : Fin n, a ∈ S l ∧ b ∈ S l) (p : Fin n) :
    (Finset.univ.filter (fun l => p ∈ S l)).card = q + 1 := by
  classical
  set L := Finset.univ.filter (fun l => p ∈ S l) with hL
  have hU : Finset.univ.erase p = L.biUnion (fun l => (S l).erase p) := by
    ext r
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_biUnion, hL,
      Finset.mem_filter, true_and]
    constructor
    · intro hr
      obtain ⟨l, ⟨h1, h2⟩, _⟩ := huniq r p hr
      exact ⟨l, h2, hr, h1⟩
    · rintro ⟨l, _, hr, _⟩
      exact hr
  have hdisj : (L : Set (Fin n)).PairwiseDisjoint (fun l => (S l).erase p) := by
    intro l hl l' hl' hne
    have hl1 : p ∈ S l := (Finset.mem_filter.1 hl).2
    have hl2 : p ∈ S l' := (Finset.mem_filter.1 hl').2
    rw [Function.onFun, Finset.disjoint_left]
    intro r hr hr'
    rw [Finset.mem_erase] at hr hr'
    obtain ⟨m, _, hm⟩ := huniq r p hr.1
    exact hne ((hm l ⟨hr.2, hl1⟩).trans (hm l' ⟨hr'.2, hl2⟩).symm)
  have hsum : (Finset.univ.erase p).card = L.card * q := by
    rw [hU, Finset.card_biUnion hdisj]
    have : ∀ l ∈ L, ((S l).erase p).card = q := by
      intro l hl
      rw [Finset.card_erase_of_mem (Finset.mem_filter.1 hl).2, hcard]
      simp
    rw [Finset.sum_congr rfl this]
    simp
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hsum
  have e : n - 1 = (q + 1) * q := by
    rw [hn, Nat.add_sub_cancel]
    ring
  rw [e] at hsum
  exact (Nat.eq_of_mul_eq_mul_right hq hsum).symm

end PEqualNP.Outside.L_meta_8541

theorem PEqualNP.Outside.L_meta_8541 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Finset (Fin x1)), (0 : ℕ) < x2 → x1 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x6 : Fin x1), (x3 x6).card = x2 + (1 : ℕ)) → (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x7 ∈ x3 x10 ∧ x8 ∈ x3 x10) → ∀ (x8 : Finset (Fin x1)) (x9 : Finset (Fin x1 × Fin x1)), (∀ x10 ∈ x9, x10.1 ∈ x8 ∧ x8 ⊆ x3 x10.2) → x9.card ≤ x2 + (1 : ℕ) := by
  intro n q S hq hn hcard huniq A P hP
  classical
  set Ls := Finset.univ.filter (fun l => A ⊆ S l) with hLs
  have hsub : P ⊆ A ×ˢ Ls := by
    intro x hx
    obtain ⟨h1, h2⟩ := hP x hx
    rw [Finset.mem_product]
    exact ⟨h1, Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_product]
  rcases Ls.eq_empty_or_nonempty with h | ⟨l0, hl0⟩
  · simp [h]
  have hA : A ⊆ S l0 := (Finset.mem_filter.1 hl0).2
  by_cases h2 : 2 ≤ A.card
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h2
    have hLsc : Ls.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro l hl l' hl'
      have h1 := (Finset.mem_filter.1 hl).2
      have h1' := (Finset.mem_filter.1 hl').2
      obtain ⟨m, _, hm⟩ := huniq a b hab
      exact (hm l ⟨h1 ha, h1 hb⟩).trans (hm l' ⟨h1' ha, h1' hb⟩).symm
    have hAc : A.card ≤ q + 1 := by
      have := Finset.card_le_card hA
      rw [hcard] at this
      exact this
    calc A.card * Ls.card ≤ (q + 1) * 1 := Nat.mul_le_mul hAc hLsc
      _ = q + 1 := by ring
  · rw [not_le] at h2
    rcases Nat.lt_or_ge A.card 1 with h0 | h1
    · have h00 : A.card = 0 := by omega
      simp [h00]
    · have hc : A.card = 1 := by omega
      obtain ⟨p, hp⟩ := Finset.card_eq_one.1 hc
      have hE : Ls = Finset.univ.filter (fun l => p ∈ S l) := by
        ext l
        simp [hLs, hp]
      rw [hc, hE, PEqualNP.Outside.L_meta_8541.through n q S hq hn hcard huniq p]
      simp
