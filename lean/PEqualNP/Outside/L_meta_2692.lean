import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_2692 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 9 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 C ∧
  (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = decide (∃ u v : Fin 7, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (2, 6)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ∧
  (∀ i : Fin C.gates.length, (i : ℕ) ≠ 8 → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, 7 + (i : ℕ)⟩ (List.ofFn x) = true → decide (∃ u v : Fin 7, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 5), (2, 6)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) = true) →
    ∀ j : Fin C.gates.length, 7 + (i : ℕ) ∈ (C.gates.get j).inputs → (j : ℕ) = 8) ∧
  (∃ i j : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ 7 + (j : ℕ) ∈ (C.gates.get i).inputs) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_, ?_, ?_, ⟨⟨7, by decide⟩, ⟨6, by decide⟩, rfl, rfl, by decide⟩⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · unfold PEqualNP.MetaComplexity.NestedCover.ReadsBack PEqualNP.MetaComplexity.NestedCover.gateAt
    decide
  · decide +kernel
  · decide +kernel
