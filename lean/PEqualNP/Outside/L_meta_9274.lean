import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9274

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- A 16 gate AND/OR circuit for the 12-cycle u-u, u-(u+1) on 6 + 6 vertices.
def circ : Circuit :=
  ⟨[⟨GateOp.or, [9, 5]⟩, ⟨GateOp.or, [12, 8]⟩, ⟨GateOp.or, [2, 11]⟩, ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [4, 13]⟩, ⟨GateOp.and, [1, 15]⟩, ⟨GateOp.or, [10, 0]⟩,
    ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.or, [19, 12]⟩, ⟨GateOp.and, [17, 14]⟩, ⟨GateOp.and, [19, 20]⟩,
    ⟨GateOp.and, [21, 16]⟩, ⟨GateOp.or, [23, 24]⟩, ⟨GateOp.or, [22, 25]⟩,
    ⟨GateOp.or, [18, 26]⟩], 27⟩

theorem circ_mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> simp

theorem circ_rep :
    Represents (fun u v : Fin 6 => (36245127555 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_9274

theorem PEqualNP.Outside.L_meta_9274 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (36245127555 : ℕ).testBit (6 * u.val + v.val)) 16 := by
  exact ⟨PEqualNP.Outside.L_meta_9274.circ, PEqualNP.Outside.L_meta_9274.circ_mono, by decide,
    PEqualNP.Outside.L_meta_9274.circ_rep⟩
