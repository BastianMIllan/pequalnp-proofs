import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1860

open PEqualNP.CircuitLowerBounds

theorem ofFn8 (x : Fin 8 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

def c1 : Circuit := { gates := [⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.and, [3, 11]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [7, 13]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 14]⟩], output := 16 }

theorem e1 : ∀ a b c d e f g h : Bool, c1.eval [a, b, c, d, e, f, g, h] = ((a && h) || (b && h) || (c && f) || (c && g) || (c && h) || (d && e) || (d && g) || (d && h)) := by
  decide

theorem f1 : PEqualNP.MetaComplexity.Monotone2 c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_1860

theorem PEqualNP.Outside.L_meta_1860 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun z : Fin 8 → Bool => (z 0 && z 7) || (z 1 && z 7) || (z 2 && z 5) || (z 2 && z 6) || (z 2 && z 7) || (z 3 && z 4) || (z 3 && z 6) || (z 3 && z 7)) x := by
  exact ⟨PEqualNP.Outside.L_meta_1860.c1, PEqualNP.Outside.L_meta_1860.f1, by decide, fun x => by rw [PEqualNP.Outside.L_meta_1860.ofFn8 x]; exact PEqualNP.Outside.L_meta_1860.e1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)⟩
