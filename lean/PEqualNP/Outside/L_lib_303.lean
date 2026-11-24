import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_303 : ∀ x : Fin 4 → Bool,
    (PEqualNP.CircuitLowerBounds.Circuit.mk [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩] 6).eval
      (List.ofFn x) =
    PEqualNP.MetaComplexity.NestedCover.graphFun (PEqualNP.EdgeOwnership.edgeGraph 4 [(0, 1), (1, 2), (2, 3), (3, 0)]) ∅ x := by
  decide
