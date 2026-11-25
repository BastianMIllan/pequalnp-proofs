import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_5424 : PEqualNP.MetaComplexity.Monotone2 ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 8] }], output := 9 } : PEqualNP.CircuitLowerBounds.Circuit) ∧
  ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 8] }], output := 9 } : PEqualNP.CircuitLowerBounds.Circuit).size = 2 ∧
  PEqualNP.Represents.Represents (fun u v : Fin 4 => (3 : ℕ).testBit (4 * u.val + v.val)) ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 8] }], output := 9 } : PEqualNP.CircuitLowerBounds.Circuit) := by
  refine ⟨?_, rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp
  · decide
