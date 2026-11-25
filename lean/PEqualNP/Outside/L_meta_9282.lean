import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9282

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- An 11 gate AND/OR circuit: three blocks {u, u+3} x {u, u+3} for u = 0, 1, 2.
def circ : Circuit :=
  ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [1, 4]⟩,
    ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.and, [15, 16]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [8, 11]⟩,
    ⟨GateOp.and, [18, 19]⟩, ⟨GateOp.or, [14, 17]⟩, ⟨GateOp.or, [21, 20]⟩], 22⟩

theorem circ_mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem circ_rep :
    Represents (fun u v : Fin 6 => (38959203465 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_9282

theorem PEqualNP.Outside.L_meta_9282 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (38959203465 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨PEqualNP.Outside.L_meta_9282.circ, PEqualNP.Outside.L_meta_9282.circ_mono, by decide,
    PEqualNP.Outside.L_meta_9282.circ_rep⟩
