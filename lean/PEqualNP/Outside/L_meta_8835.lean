import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8835

theorem key (x1 : Type) (x2 x3 : ℕ) (x5 : ℕ → Set x1)
    (hg : ∀ x7 < x3, ∃ x9 < x2 + x7, ∃ x10 < x2 + x7, x5 (x2 + x7) = x5 x9 ∪ x5 x10 ∨ x5 (x2 + x7) = x5 x9 ∨ x5 (x2 + x7) = ∅ ∨ x5 (x2 + x7) = x5 x9 ∩ x5 x10) :
    ∀ k ≤ x3, ∃ lab nl : ℕ → ℕ, x2 ≤ ((Finset.range x2).image lab).card + k ∧
      ∀ j < x2 + k, ∀ a b : x1, (∀ i < x2, lab i = nl j → (a ∈ x5 i ↔ b ∈ x5 i)) →
        (a ∈ x5 j ↔ b ∈ x5 j) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨id, id, ?_, ?_⟩
    · simp
    · intro j hj a b h
      exact h j (by omega) rfl
  | succ k ih =>
    intro hk
    obtain ⟨lab, nl, hA, hB⟩ := ih (by omega)
    obtain ⟨x9, h9, x10, h10, hcase⟩ := hg k (by omega)
    obtain ⟨p, hp⟩ : ∃ p, p = nl x9 := ⟨_, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q, q = nl x10 := ⟨_, rfl⟩
    refine ⟨fun i => if lab i = q then p else lab i,
      fun j => if j = x2 + k then p else if nl j = q then p else nl j, ?_, ?_⟩
    · have hsub : (Finset.range x2).image lab ⊆
          insert q ((Finset.range x2).image (fun i => if lab i = q then p else lab i)) := by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_range] at hx ⊢
        obtain ⟨i, hi, rfl⟩ := hx
        by_cases h : lab i = q
        · left; exact h
        · right; exact ⟨i, hi, by simp [h]⟩
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_insert_le q
        ((Finset.range x2).image (fun i => if lab i = q then p else lab i))
      omega
    · intro j hj a b h
      have h' : ∀ i < x2, (if lab i = q then p else lab i) =
          (if j = x2 + k then p else if nl j = q then p else nl j) → (a ∈ x5 i ↔ b ∈ x5 i) := h
      rcases Nat.lt_or_ge j (x2 + k) with hjl | hjg
      · apply hB j hjl a b
        intro i hi hl
        apply h' i hi
        rw [if_neg (show ¬ (j = x2 + k) by omega)]
        by_cases hqq : nl j = q
        · rw [if_pos hqq, if_pos (hl.trans hqq)]
        · rw [if_neg hqq, if_neg (show ¬ (lab i = q) by rw [hl]; exact hqq)]
          exact hl
      · obtain rfl : j = x2 + k := by omega
        rw [if_pos rfl] at h'
        have e : ∀ i, lab i = p ∨ lab i = q → (if lab i = q then p else lab i) = p := by
          intro i hi
          split_ifs with hh
          · rfl
          · rcases hi with hi | hi
            · exact hi
            · exact absurd hi hh
        have A9 := hB x9 h9 a b (fun i hi hl => h' i hi (e i (Or.inl (hl.trans hp.symm))))
        have A10 := hB x10 h10 a b (fun i hi hl => h' i hi (e i (Or.inr (hl.trans hq.symm))))
        rcases hcase with e1 | e1 | e1 | e1
        · rw [e1, Set.mem_union, Set.mem_union, A9, A10]
        · rw [e1, A9]
        · rw [e1]; simp
        · rw [e1, Set.mem_inter_iff, Set.mem_inter_iff, A9, A10]

end PEqualNP.Outside.L_meta_8835

theorem PEqualNP.Outside.L_meta_8835 : ∀ (x1 : Type) (x2 x3 x4 : ℕ) (x5 : ℕ → Set x1), x4 < x2 + x3 → (∀ x7 < x3, ∃ x9 < x2 + x7, ∃ x10 < x2 + x7, x5 (x2 + x7) = x5 x9 ∪ x5 x10 ∨ x5 (x2 + x7) = x5 x9 ∨ x5 (x2 + x7) = ∅ ∨ x5 (x2 + x7) = x5 x9 ∩ x5 x10) → (∀ x8 < x2, ∃ (x10 : x1) (x11 : x1), (∀ x12 < x2, x12 ≠ x8 → (x10 ∈ x5 x12 ↔ x11 ∈ x5 x12)) ∧ x10 ∈ x5 x4 ∧ x11 ∉ x5 x4) → x2 ≤ x3 + (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 h4 hg hd
  obtain ⟨lab, nl, hA, hB⟩ := PEqualNP.Outside.L_meta_8835.key x1 x2 x3 x5 hg x3 le_rfl
  have hall : ∀ i < x2, lab i = nl x4 := by
    intro i hi
    by_contra hne
    obtain ⟨a, b, hab, ha, hb⟩ := hd i hi
    exact hb ((hB x4 h4 a b (fun i' hi' hl => hab i' hi' (by rintro rfl; exact hne hl))).mp ha)
  have hsub : (Finset.range x2).image lab ⊆ {nl x4} := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_singleton] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    exact hall i hi
  have hc := Finset.card_le_card hsub
  rw [Finset.card_singleton] at hc
  omega
