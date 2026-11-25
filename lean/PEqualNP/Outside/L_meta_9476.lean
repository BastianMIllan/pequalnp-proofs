import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9476

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Median of five: sort the pairs (0,1) and (2,3), drop the least of the two minima and the
-- greatest of the two maxima, and take the median of the remaining two with input 4.
def circ : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.and, [9, 10]⟩, ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.and, [4, 12]⟩, ⟨GateOp.or, [11, 13]⟩], 14⟩

theorem circ_fan : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem circ_eval : ∀ x : Fin 5 → Bool,
    circ.eval (List.ofFn x) = decide (3 ≤ ((List.ofFn x).count true)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_9476

theorem PEqualNP.Outside.L_meta_9476 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => decide (3 ≤ ((List.ofFn x).count true))) 12 := by
  exact ⟨PEqualNP.Outside.L_meta_9476.circ, PEqualNP.Outside.L_meta_9476.circ_fan, by decide,
    PEqualNP.Outside.L_meta_9476.circ_eval⟩
