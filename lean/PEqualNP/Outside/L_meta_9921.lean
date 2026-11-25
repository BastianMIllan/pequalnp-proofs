import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9921

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Bitwise equality: for each bit i the gates (a AND b) OR NOT (a OR b) test x i = x (i+3),
-- and two AND gates join the three tests. Four gates per bit and two more: 14 gates.
def circ : Circuit :=
  ⟨[⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.or, [6, 8]⟩,
    ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.not, [15]⟩, ⟨GateOp.or, [14, 16]⟩,
    ⟨GateOp.and, [9, 13]⟩, ⟨GateOp.and, [18, 17]⟩], 19⟩

theorem circ_fan : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem circ_eval : ∀ x : Fin 6 → Bool,
    circ.eval (List.ofFn x) = decide ((1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat) = (1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_9921

theorem PEqualNP.Outside.L_meta_9921 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => decide ((1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat) = (1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat))) 14 := by
  exact ⟨PEqualNP.Outside.L_meta_9921.circ, PEqualNP.Outside.L_meta_9921.circ_fan, by decide,
    PEqualNP.Outside.L_meta_9921.circ_eval⟩
