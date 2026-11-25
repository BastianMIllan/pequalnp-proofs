import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_6024 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → x1.gates = [] → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C x2 _ _ hg
  have hw : ∀ x, C.eval x = x.getD C.output false := by
    intro x
    simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, hg]
  by_cases h10 : C.output < 10
  · refine ⟨fun i => decide (i = x2 ⟨C.output, h10⟩), ?_⟩
    have hl : C.output < (List.ofFn ((fun i => decide (i = x2 ⟨C.output, h10⟩)) ∘ x2)).length := by
      simpa using h10
    rw [hw, List.getD_append _ _ _ _ hl, List.getD_eq_getElem _ _ hl]
    simp only [List.getElem_ofFn, Function.comp]
    generalize x2 ⟨C.output, h10⟩ = v
    revert v
    decide
  · by_cases h11 : C.output = 10
    · refine ⟨fun i => decide (i = 0) || decide (i = 1), ?_⟩
      rw [hw, h11, List.getD_append_right _ _ _ _ (by simp)]
      simp only [List.length_ofFn]
      decide
    · refine ⟨fun _ => true, ?_⟩
      rw [hw, List.getD_eq_default _ _ (by simp; omega)]
      decide
