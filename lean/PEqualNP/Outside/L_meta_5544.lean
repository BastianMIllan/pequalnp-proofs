import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.L_meta_5544 : PEqualNP.MetaComplexity.Monotone2 ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }], output := 8 } : PEqualNP.CircuitLowerBounds.Circuit) ∧
  ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }], output := 8 } : PEqualNP.CircuitLowerBounds.Circuit).size = 1 ∧
  PEqualNP.Represents.Represents (fun u v : Fin 4 => (255 : ℕ).testBit (4 * u.val + v.val)) ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }], output := 8 } : PEqualNP.CircuitLowerBounds.Circuit) := by
  refine ⟨?_, rfl, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
