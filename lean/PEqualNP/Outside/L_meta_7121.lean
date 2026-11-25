import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7121

def orCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }], output := 8 }

end PEqualNP.Outside.L_meta_7121

theorem PEqualNP.Outside.L_meta_7121 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (1 : ℕ) ∧ ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2) = (x2 (0 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ))) := by
  refine ⟨PEqualNP.Outside.L_meta_7121.orCircuit, ?_, ?_, ?_⟩
  · intro g hg
    simp [PEqualNP.Outside.L_meta_7121.orCircuit] at hg
    subst hg
    simp
  · decide
  · intro x
    first
      | (simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
          PEqualNP.Outside.L_meta_7121.orCircuit, PEqualNP.CircuitLowerBounds.GateOp.eval, List.ofFn_succ]; done)
      | rfl
