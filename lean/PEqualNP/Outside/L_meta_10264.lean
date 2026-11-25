import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10264

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- bit 2 = (a2 b0 xor a0 b2) xor (a1 b1 and not (a0 b0))
def C0 : Circuit := ⟨[⟨GateOp.and, [0, 3]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [8, 7]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.and, [12, 14]⟩, ⟨GateOp.or, [15, 9]⟩, ⟨GateOp.and, [15, 9]⟩, ⟨GateOp.not, [17]⟩, ⟨GateOp.and, [16, 18]⟩], 19⟩

theorem ok0 : FanInTwo C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev0 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C0.eval [b0, b1, b2, b3, b4, b5] = Nat.testBit ((1 * b0.toNat + 2 * b1.toNat + 4 * b2.toNat) * (1 * b3.toNat + 2 * b4.toNat + 4 * b5.toNat)) 2 := by
  decide +kernel

theorem ofFn6 (x : Fin 6 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
  simp [List.ofFn_succ]

end PEqualNP.Outside.L_meta_10264

theorem PEqualNP.Outside.L_meta_10264 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit ((1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat) * (1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat)) 2) 16 :=
  ⟨PEqualNP.Outside.L_meta_10264.C0, PEqualNP.Outside.L_meta_10264.ok0, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_10264.ofFn6]
      exact PEqualNP.Outside.L_meta_10264.ev0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩
