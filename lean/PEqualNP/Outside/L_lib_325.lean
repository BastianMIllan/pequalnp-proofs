import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_lib_325 : PEqualNP.TopForm.IsAO2 14 (PEqualNP.CircuitLowerBounds.Circuit.mk [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 15]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 23]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 6]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 35]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 27]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [42, 36]⟩] 43) := by
  decide +kernel
