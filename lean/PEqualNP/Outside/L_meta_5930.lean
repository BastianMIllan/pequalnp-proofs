import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_5930 : ∀ (x1 : List ℕ) (x2 x3 : ℕ), x3 < x1.length → (x1 ++ [x2]).getD x3 (0 : ℕ) = x1.getD x3 (0 : ℕ) := by
  intro x1 x2 x3 h
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h,
    List.getElem_append_left h]
