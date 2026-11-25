import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10258

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Bit 2 of the product is the parity of a2 b0, a0 b2, a1 b1 and the column-1 carry
-- a1 b0 a0 b1. Since a1 b1 XOR a0 a1 b0 b1 = a1 b1 AND NOT (a0 b0), it is
-- a2 b0 XOR a0 b2 XOR (a1 b1 AND NOT a0 b0): six gates and two XORs of four gates, 14 gates.
def circ : Circuit :=
  ⟨[⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [0, 3]⟩,
    ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [8, 10]⟩,
    ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.and, [12, 14]⟩,
    ⟨GateOp.or, [15, 11]⟩, ⟨GateOp.and, [15, 11]⟩, ⟨GateOp.not, [17]⟩, ⟨GateOp.and, [16, 18]⟩], 19⟩

theorem circ_fan : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem circ_eval : ∀ x : Fin 6 → Bool,
    circ.eval (List.ofFn x) = Nat.testBit ((1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat) * (1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat)) 2 := by
  decide +kernel

end PEqualNP.Outside.L_meta_10258

theorem PEqualNP.Outside.L_meta_10258 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit ((1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat) * (1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat)) 2) 17 := by
  exact ⟨PEqualNP.Outside.L_meta_10258.circ, PEqualNP.Outside.L_meta_10258.circ_fan, by decide,
    PEqualNP.Outside.L_meta_10258.circ_eval⟩
