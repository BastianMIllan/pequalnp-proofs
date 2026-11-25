import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6750

theorem key {α : Type*} [DecidableEq α] (x3 : ℕ → Finset α) :
    ∀ (n : ℕ) (x1 : Finset α) (x2 : Finset ℕ), x1.card = n →
      ∃ x4 ⊆ x1, (x1 \ x4).card ≤ (x2.filter fun y => Disjoint x4 (x3 y)).card ∧
        ∀ y ∈ x2, (x4 ∩ x3 y).card ≠ 1 := by
  intro n
  induction n with
  | zero =>
    intro x1 x2 hn
    have h0 : x1 = ∅ := Finset.card_eq_zero.mp hn
    subst h0
    refine ⟨∅, Finset.Subset.refl _, by simp, ?_⟩
    intro y _
    simp
  | succ k ih =>
    intro x1 x2 hn
    by_cases h : ∃ y ∈ x2, (x1 ∩ x3 y).card = 1
    · obtain ⟨y, hy, hc⟩ := h
      obtain ⟨e, he⟩ := Finset.card_eq_one.mp hc
      have heI : e ∈ x1 ∩ x3 y := by rw [he]; exact Finset.mem_singleton_self e
      have hex : e ∈ x1 := (Finset.mem_inter.mp heI).1
      have hcard' : (x1.erase e).card = k := by
        rw [Finset.card_erase_of_mem hex, hn]; rfl
      obtain ⟨x4, hsub, hle, hall⟩ := ih (x1.erase e) (x2.erase y) hcard'
      have he4 : e ∉ x4 := fun h4 => Finset.notMem_erase e x1 (hsub h4)
      have hdis : Disjoint x4 (x3 y) := by
        rw [Finset.disjoint_left]
        intro z hz4 hz3
        have hz1 : z ∈ x1 := Finset.mem_of_mem_erase (hsub hz4)
        have hzI : z ∈ x1 ∩ x3 y := Finset.mem_inter.mpr ⟨hz1, hz3⟩
        rw [he] at hzI
        have : z = e := Finset.mem_singleton.mp hzI
        exact he4 (this ▸ hz4)
      refine ⟨x4, hsub.trans (Finset.erase_subset e x1), ?_, ?_⟩
      · have hA : x1 \ x4 = insert e (x1.erase e \ x4) := by
          ext z
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro ⟨hz1, hz4⟩
            by_cases hze : z = e
            · exact Or.inl hze
            · exact Or.inr ⟨⟨hze, hz1⟩, hz4⟩
          · rintro (hze | ⟨⟨_, hz1⟩, hz4⟩)
            · subst hze; exact ⟨hex, he4⟩
            · exact ⟨hz1, hz4⟩
        have hA2 : e ∉ x1.erase e \ x4 := by
          intro hm
          exact Finset.notMem_erase e x1 (Finset.mem_sdiff.mp hm).1
        have hB : insert y ((x2.erase y).filter fun y' => Disjoint x4 (x3 y')) ⊆
            x2.filter fun y' => Disjoint x4 (x3 y') := by
          intro z hz
          rw [Finset.mem_insert] at hz
          rcases hz with hz | hz
          · subst hz; exact Finset.mem_filter.mpr ⟨hy, hdis⟩
          · have hz' := Finset.mem_filter.mp hz
            exact Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hz'.1, hz'.2⟩
        have hB2 : y ∉ (x2.erase y).filter fun y' => Disjoint x4 (x3 y') := by
          intro hm
          exact Finset.notMem_erase y x2 (Finset.mem_filter.mp hm).1
        have hB3 := Finset.card_le_card hB
        rw [Finset.card_insert_of_notMem hB2] at hB3
        rw [hA, Finset.card_insert_of_notMem hA2]
        omega
      · intro z hz
        by_cases hzy : z = y
        · subst hzy
          rw [Finset.disjoint_iff_inter_eq_empty.mp hdis]
          simp
        · exact hall z (Finset.mem_erase.mpr ⟨hzy, hz⟩)
    · push_neg at h
      refine ⟨x1, Finset.Subset.refl _, by simp, h⟩

end PEqualNP.Outside.L_meta_6750

theorem PEqualNP.Outside.L_meta_6750 : ∀ (x1 : Finset (Sym2 (Fin (11 : ℕ)))) (x2 : Finset ℕ) (x3 : ℕ → Finset (Sym2 (Fin (11 : ℕ)))), ∃ x4 ⊆ x1, (x1 \ x4).card ≤ {x5 ∈ x2 | Disjoint x4 (x3 x5)}.card ∧ ∀ x5 ∈ x2, (x4 ∩ x3 x5).card ≠ (1 : ℕ) := by
  intro x1 x2 x3
  exact PEqualNP.Outside.L_meta_6750.key x3 x1.card x1 x2 rfl
