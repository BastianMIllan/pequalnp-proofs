import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_8787 : ∀ (x1 : List ℕ) (x2 : ℕ),   have x3 : (ℕ → Prop) → (ℕ → Prop) → ℕ → Prop := fun (x3 x4 : ℕ → Prop) (x5 : ℕ) => ∃ (x6 : ℕ), x3 x6 ∧ ∃ (x7 : ℕ), x4 x7 ∧ (x5 = x6 &&& x7 ∨ x5 = x6 ||| x7);   have x4 : List ℕ → ℕ → Prop := fun (x4 : List ℕ) => x3 (fun (x5 : ℕ) => x5 ∈ x4) fun (x5 : ℕ) => x5 ∈ x4;   (have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 ∈ x1;     have x6 : ℕ → Prop := x3 x5 x5;     x3 x6 x6 x2 ∨ x3 x5 (x3 x5 x6) x2) →     ∃ (x6 : List ℕ), x6.length ≤ (2 : ℕ) ∧ (∀ (x7 : Fin x6.length), x4 (x1 ++ List.take (↑x7) x6) (x6.get x7)) ∧ x4 (x1 ++ x6) x2 := by
  intro x1 x2
  dsimp only
  rintro (⟨c, ⟨a1, ha1, b1, hb1, hc⟩, d, ⟨a2, ha2, b2, hb2, hd⟩, hx⟩ |
      ⟨a, ha, e, ⟨b, hb, c, ⟨a3, ha3, b3, hb3, hc⟩, he⟩, hx⟩)
  · refine ⟨[c, d], by simp, ?_, ?_⟩
    · intro k
      fin_cases k
      · exact ⟨a1, by simp [ha1], b1, by simp [hb1], hc⟩
      · exact ⟨a2, by simp [ha2], b2, by simp [hb2], hd⟩
    · exact ⟨c, by simp, d, by simp, hx⟩
  · refine ⟨[c, e], by simp, ?_, ?_⟩
    · intro k
      fin_cases k
      · exact ⟨a3, by simp [ha3], b3, by simp [hb3], hc⟩
      · exact ⟨b, by simp [hb], c, by simp, he⟩
    · exact ⟨a, by simp [ha], e, by simp, hx⟩
