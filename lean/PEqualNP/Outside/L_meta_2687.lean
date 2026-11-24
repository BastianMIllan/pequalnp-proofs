import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_2687 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 12] }], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 8 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 C ∧
  (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) ∧
  (∀ i : Fin C.gates.length, (i : ℕ) ≠ 7 → (∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, 6 + (i : ℕ)⟩ (List.ofFn x) = true → decide (∃ u v : Fin 6, ((u : ℕ), (v : ℕ)) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) = true) →
    ∀ j : Fin C.gates.length, 6 + (i : ℕ) ∈ (C.gates.get j).inputs → (j : ℕ) = 7) ∧
  (∃ i j : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ 6 + (j : ℕ) ∈ (C.gates.get i).inputs) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_, ?_, ?_, ⟨⟨6, by decide⟩, ⟨5, by decide⟩, rfl, rfl, by decide⟩⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · unfold PEqualNP.MetaComplexity.NestedCover.ReadsBack PEqualNP.MetaComplexity.NestedCover.gateAt
    decide
  · decide +kernel
  · decide +kernel
