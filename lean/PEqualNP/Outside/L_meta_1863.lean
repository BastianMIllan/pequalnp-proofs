import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1863

open PEqualNP.CircuitLowerBounds

theorem ofFn8 (x : Fin 8 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

def c1 : Circuit := { gates := [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [8, 7]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.and, [10, 13]⟩, ⟨GateOp.or, [9, 14]⟩], output := 15 }

theorem e1 : ∀ a b c d e f g h : Bool, c1.eval [a, b, c, d, e, f, g, h] = ((a && h) || (b && h) || (c && e) || (c && f) || (c && g) || (c && h) || (d && e) || (d && f) || (d && g) || (d && h)) := by
  decide

theorem f1 : PEqualNP.MetaComplexity.Monotone2 c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_1863

theorem PEqualNP.Outside.L_meta_1863 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun z : Fin 8 → Bool => (z 0 && z 7) || (z 1 && z 7) || (z 2 && z 4) || (z 2 && z 5) || (z 2 && z 6) || (z 2 && z 7) || (z 3 && z 4) || (z 3 && z 5) || (z 3 && z 6) || (z 3 && z 7)) x := by
  exact ⟨PEqualNP.Outside.L_meta_1863.c1, PEqualNP.Outside.L_meta_1863.f1, by decide, fun x => by rw [PEqualNP.Outside.L_meta_1863.ofFn8 x]; exact PEqualNP.Outside.L_meta_1863.e1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)⟩
