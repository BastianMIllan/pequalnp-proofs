import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1852

open PEqualNP.CircuitLowerBounds

theorem ofFn7 (x : Fin 7 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
  simp [List.ofFn_succ]

def c1 : Circuit := { gates := [⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [6, 10]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 13]⟩], output := 15 }

theorem e1 : ∀ a b c d e f g : Bool, c1.eval [a, b, c, d, e, f, g] = ((a && f) || (a && g) || (b && d) || (b && e) || (b && g) || (c && d) || (c && e) || (c && f)) := by
  decide

theorem f1 : PEqualNP.MetaComplexity.Monotone2 c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_1852

theorem PEqualNP.Outside.L_meta_1852 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun z : Fin 7 → Bool => (z 0 && z 5) || (z 0 && z 6) || (z 1 && z 3) || (z 1 && z 4) || (z 1 && z 6) || (z 2 && z 3) || (z 2 && z 4) || (z 2 && z 5)) x := by
  exact ⟨PEqualNP.Outside.L_meta_1852.c1, PEqualNP.Outside.L_meta_1852.f1, by decide, fun x => by rw [PEqualNP.Outside.L_meta_1852.ofFn7 x]; exact PEqualNP.Outside.L_meta_1852.e1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)⟩
