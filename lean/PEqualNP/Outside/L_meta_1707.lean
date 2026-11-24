import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1707

theorem bad (A m : Finset (Fin 21)) (a b c : Fin 21) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (ham : a ∈ m) (hbm : b ∈ m) (hcm : c ∈ m)
    (h : (A ∩ m).card ≤ 2) : False := by
  have hs : ({a, b, c} : Finset (Fin 21)) ⊆ A ∩ m := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hz
    rw [Finset.mem_inter]
    rcases hz with rfl | rfl | rfl
    · exact ⟨ha, ham⟩
    · exact ⟨hb, hbm⟩
    · exact ⟨hc, hcm⟩
  have h3 : ({a, b, c} : Finset (Fin 21)).card = 3 := Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have h4 := Finset.card_le_card hs
  omega

end PEqualNP.Outside.L_meta_1707

set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_1707 : (∀ A : Finset (Fin 21), (∀ m ∈ ([{1, 5, 9, 13, 17}, {0, 5, 6, 7, 8}, {2, 5, 10, 15, 20}, {4, 5, 12, 14, 19}, {3, 5, 11, 16, 18}, {0, 1, 2, 3, 4}, {1, 6, 10, 14, 18}, {1, 8, 12, 16, 20}, {1, 7, 11, 15, 19}, {0, 9, 10, 11, 12}, {2, 6, 9, 16, 19}, {4, 8, 9, 15, 18}, {3, 7, 9, 14, 20}, {0, 17, 18, 19, 20}, {3, 6, 12, 15, 17}, {2, 8, 11, 14, 17}, {4, 7, 10, 16, 17}, {0, 13, 14, 15, 16}, {4, 6, 11, 13, 20}, {3, 8, 10, 13, 19}, {2, 7, 12, 13, 18}] : List (Finset (Fin 21))), (A ∩ m).card ≤ 2) ∧ (∀ p ∈ A, p ∉ ({1, 5, 9, 13, 17} : Finset (Fin 21))) ∧ ({3, 4, 11} : Finset (Fin 21)) ⊆ A → (A ∩ ({0, 6, 7, 8} : Finset (Fin 21)) = ∅ ∨ A ∩ ({2, 10, 15, 20} : Finset (Fin 21)) = ∅)) ∧ ∃ A : Finset (Fin 21), (∀ m ∈ ([{1, 5, 9, 13, 17}, {0, 5, 6, 7, 8}, {2, 5, 10, 15, 20}, {4, 5, 12, 14, 19}, {3, 5, 11, 16, 18}, {0, 1, 2, 3, 4}, {1, 6, 10, 14, 18}, {1, 8, 12, 16, 20}, {1, 7, 11, 15, 19}, {0, 9, 10, 11, 12}, {2, 6, 9, 16, 19}, {4, 8, 9, 15, 18}, {3, 7, 9, 14, 20}, {0, 17, 18, 19, 20}, {3, 6, 12, 15, 17}, {2, 8, 11, 14, 17}, {4, 7, 10, 16, 17}, {0, 13, 14, 15, 16}, {4, 6, 11, 13, 20}, {3, 8, 10, 13, 19}, {2, 7, 12, 13, 18}] : List (Finset (Fin 21))), (A ∩ m).card ≤ 2) ∧ (∀ p ∈ A, p ∉ ({1, 5, 9, 13, 17} : Finset (Fin 21))) ∧ ({3, 4, 11} : Finset (Fin 21)) ⊆ A := by
  refine ⟨?_, {3, 4, 11}, ?_, by decide, Finset.Subset.refl _⟩
  rotate_left
  · intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  intro A ⟨hA, _, hsub⟩
  have h3 : (3 : Fin 21) ∈ A := hsub (by decide)
  have h4 : (4 : Fin 21) ∈ A := hsub (by decide)
  have h11 : (11 : Fin 21) ∈ A := hsub (by decide)
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hx, hy⟩ := hcon
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hx
  obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hy
  rw [Finset.mem_inter] at hx hy
  obtain ⟨hxA, hxX⟩ := hx
  obtain ⟨hyA, hyY⟩ := hy
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hxX hyY
  rcases hxX with rfl | rfl | rfl | rfl
  · exact PEqualNP.Outside.L_meta_1707.bad A ({0, 1, 2, 3, 4} : Finset (Fin 21)) _ _ _ (by decide) (by decide) (by decide) h3 h4 hxA (by decide) (by decide) (by decide) (hA _ (by simp only [List.mem_cons, true_or, or_true]))
  · exact PEqualNP.Outside.L_meta_1707.bad A ({4, 6, 11, 13, 20} : Finset (Fin 21)) _ _ _ (by decide) (by decide) (by decide) h4 h11 hxA (by decide) (by decide) (by decide) (hA _ (by simp only [List.mem_cons, true_or, or_true]))
  · rcases hyY with rfl | rfl | rfl | rfl
    · exact PEqualNP.Outside.L_meta_1707.bad A ({0, 1, 2, 3, 4} : Finset (Fin 21)) _ _ _ (by decide) (by decide) (by decide) h3 h4 hyA (by decide) (by decide) (by decide) (hA _ (by simp only [List.mem_cons, true_or, or_true]))
    · exact PEqualNP.Outside.L_meta_1707.bad A ({4, 7, 10, 16, 17} : Finset (Fin 21)) _ _ _ (by decide) (by decide) (by decide) h4 hxA hyA (by decide) (by decide) (by decide) (hA _ (by simp only [List.mem_cons, true_or, or_true]))
    · exact PEqualNP.Outside.L_meta_1707.bad A ({1, 7, 11, 15, 19} : Finset (Fin 21)) _ _ _ (by decide) (by decide) (by decide) h11 hxA hyA (by decide) (by decide) (by decide) (hA _ (by simp only [List.mem_cons, true_or, or_true]))
    · exact PEqualNP.Outside.L_meta_1707.bad A ({4, 6, 11, 13, 20} : Finset (Fin 21)) _ _ _ (by decide) (by decide) (by decide) h4 h11 hyA (by decide) (by decide) (by decide) (hA _ (by simp only [List.mem_cons, true_or, or_true]))
  · rcases hyY with rfl | rfl | rfl | rfl
    · exact PEqualNP.Outside.L_meta_1707.bad A ({0, 1, 2, 3, 4} : Finset (Fin 21)) _ _ _ (by decide) (by decide) (by decide) h3 h4 hyA (by decide) (by decide) (by decide) (hA _ (by simp only [List.mem_cons, true_or, or_true]))
    · exact PEqualNP.Outside.L_meta_1707.bad A ({3, 8, 10, 13, 19} : Finset (Fin 21)) _ _ _ (by decide) (by decide) (by decide) h3 hxA hyA (by decide) (by decide) (by decide) (hA _ (by simp only [List.mem_cons, true_or, or_true]))
    · exact PEqualNP.Outside.L_meta_1707.bad A ({4, 8, 9, 15, 18} : Finset (Fin 21)) _ _ _ (by decide) (by decide) (by decide) h4 hxA hyA (by decide) (by decide) (by decide) (hA _ (by simp only [List.mem_cons, true_or, or_true]))
    · exact PEqualNP.Outside.L_meta_1707.bad A ({4, 6, 11, 13, 20} : Finset (Fin 21)) _ _ _ (by decide) (by decide) (by decide) h4 h11 hyA (by decide) (by decide) (by decide) (hA _ (by simp only [List.mem_cons, true_or, or_true]))
