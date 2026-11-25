import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10262

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- products p01 p10 p02 p20 p11 p12 p21, c1 = p01 and p10
-- s, t = half adder of p02, p20 ; z = c1 or (s and p11) ; bit 3 = (t xor z) xor (p12 xor p21)
def C0 : Circuit := ⟨[⟨GateOp.and, [0, 4]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.and, [9, 10]⟩, ⟨GateOp.not, [15]⟩, ⟨GateOp.and, [14, 16]⟩, ⟨GateOp.and, [17, 11]⟩, ⟨GateOp.or, [18, 8]⟩, ⟨GateOp.or, [15, 19]⟩, ⟨GateOp.and, [15, 19]⟩, ⟨GateOp.not, [21]⟩, ⟨GateOp.and, [20, 22]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.not, [25]⟩, ⟨GateOp.and, [24, 26]⟩, ⟨GateOp.or, [23, 27]⟩, ⟨GateOp.and, [23, 27]⟩, ⟨GateOp.not, [29]⟩, ⟨GateOp.and, [28, 30]⟩], 31⟩

theorem ok0 : FanInTwo C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev0 : ∀ b0 b1 b2 b3 b4 b5 : Bool,
    C0.eval [b0, b1, b2, b3, b4, b5] = Nat.testBit ((1 * b0.toNat + 2 * b1.toNat + 4 * b2.toNat) * (1 * b3.toNat + 2 * b4.toNat + 4 * b5.toNat)) 3 := by
  decide +kernel

theorem ofFn6 (x : Fin 6 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
  simp [List.ofFn_succ]

end PEqualNP.Outside.L_meta_10262

theorem PEqualNP.Outside.L_meta_10262 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit ((1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat) * (1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat)) 3) 29 :=
  ⟨PEqualNP.Outside.L_meta_10262.C0, PEqualNP.Outside.L_meta_10262.ok0, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_10262.ofFn6]
      exact PEqualNP.Outside.L_meta_10262.ev0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)⟩
