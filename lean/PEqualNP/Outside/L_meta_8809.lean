import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8809

def P {α : Type} (S : ℕ → Set α) (s : Finset ℕ) (w : ℕ) : Prop :=
  ∀ a b : α, (∀ i ∈ s, a ∈ S i → b ∈ S i) → a ∈ S w → b ∈ S w

theorem key {α : Type} (x2 x3 : ℕ) (S : ℕ → Set α)
    (h : ∀ x7 < x3, ∃ x9 < x2 + x7, ∃ x10 < x2 + x7, S (x2 + x7) = S x9 ∪ S x10 ∨
      S (x2 + x7) = S x9 ∨ S (x2 + x7) = ∅ ∨ S (x2 + x7) = S x9 ∩ S x10) :
    ∀ k, k ≤ x3 → ∀ T : Finset ℕ, (∀ w ∈ T, w < x2 + k) →
      ∃ s ⊆ Finset.range x2, s.card ≤ T.card + k ∧ ∀ w ∈ T, P S s w := by
  intro k
  induction k with
  | zero =>
    intro _ T hT
    refine ⟨T, ?_, by simp, ?_⟩
    · intro w hw; simpa using hT w hw
    · intro w hw a b hab ha; exact hab w hw ha
  | succ k ih =>
    intro hk T hT
    by_cases htop : x2 + k ∈ T
    · obtain ⟨x9, h9, x10, h10, hcase⟩ := h k (by omega)
      have hT'lt : ∀ w ∈ (T.erase (x2 + k)) ∪ {x9, x10}, w < x2 + k := by
        intro w hw
        rw [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with ⟨hne, hw⟩ | rfl | rfl
        · have := hT w hw; omega
        · exact h9
        · exact h10
      obtain ⟨s, hs, hcard, hP⟩ := ih (by omega) _ hT'lt
      have hc1 : ((T.erase (x2 + k)) ∪ {x9, x10}).card ≤ (T.erase (x2 + k)).card + 2 := by
        have h1 := Finset.card_union_le (T.erase (x2 + k)) ({x9, x10} : Finset ℕ)
        have h2 := Finset.card_insert_le x9 ({x10} : Finset ℕ)
        simp only [Finset.card_singleton] at h2
        omega
      have hc2 : (T.erase (x2 + k)).card + 1 = T.card := Finset.card_erase_add_one htop
      refine ⟨s, hs, by omega, ?_⟩
      intro w hw
      by_cases hwt : w = x2 + k
      · subst hwt
        have p9 : P S s x9 := hP x9 (by simp)
        have p10 : P S s x10 := hP x10 (by simp)
        intro a b hab ha
        rcases hcase with e | e | e | e
        · rw [e] at ha ⊢
          rcases ha with ha | ha
          · exact Or.inl (p9 a b hab ha)
          · exact Or.inr (p10 a b hab ha)
        · rw [e] at ha ⊢
          exact p9 a b hab ha
        · rw [e] at ha
          simp at ha
        · rw [e] at ha ⊢
          exact ⟨p9 a b hab ha.1, p10 a b hab ha.2⟩
      · exact hP w (by simp [hw, hwt])
    · obtain ⟨s, hs, hcard, hP⟩ := ih (by omega) T (by
        intro w hw
        have h1 := hT w hw
        have h2 : w ≠ x2 + k := fun e => htop (e ▸ hw)
        omega)
      exact ⟨s, hs, by omega, hP⟩

end PEqualNP.Outside.L_meta_8809

theorem PEqualNP.Outside.L_meta_8809 : ∀ (x1 : Type) (x2 x3 x4 : ℕ) (x5 : ℕ → Set x1), x4 < x2 + x3 → (∀ x7 < x3, ∃ x9 < x2 + x7, ∃ x10 < x2 + x7, x5 (x2 + x7) = x5 x9 ∪ x5 x10 ∨ x5 (x2 + x7) = x5 x9 ∨ x5 (x2 + x7) = ∅ ∨ x5 (x2 + x7) = x5 x9 ∩ x5 x10) → ∃ x8 ⊆ Finset.range x2, x8.card ≤ x3 + (1 : ℕ) ∧ ∀ (x9 x10 : x1), (∀ x11 ∈ x8, x9 ∈ x5 x11 → x10 ∈ x5 x11) → x9 ∈ x5 x4 → x10 ∈ x5 x4 := by
  intro x1 x2 x3 x4 x5 h4 hg
  obtain ⟨s, hs, hc, hP⟩ :=
    PEqualNP.Outside.L_meta_8809.key x2 x3 x5 hg x3 le_rfl {x4} (by simpa using h4)
  refine ⟨s, hs, ?_, ?_⟩
  · simp only [Finset.card_singleton] at hc
    omega
  · intro a b hab ha
    exact hP x4 (by simp) a b hab ha
