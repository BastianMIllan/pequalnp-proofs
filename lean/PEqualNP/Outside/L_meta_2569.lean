import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2569

open PEqualNP.CircuitLowerBounds

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem?_getD]
  simp

end PEqualNP.Outside.L_meta_2569

theorem PEqualNP.Outside.L_meta_2569 : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x1) (x5 : PEqualNP.CircuitLowerBounds.GateOp) (x6 : PEqualNP.CircuitLowerBounds.Circuit), x5 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5 = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.Monotone2 x6 → x6.size ≤ x2 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x2 + (1 : ℕ) ∧ ∀ (x11 : Fin x1 → Bool), x10.eval (List.ofFn x11) = x6.eval (List.ofFn x11 ++ [x5.eval [x11 x3, x11 x4]]) := by
  intro x1 x2 x3 x4 x5 x6 hop hmono hsize
  refine ⟨⟨⟨x5, [x3.val, x4.val]⟩ :: x6.gates, x6.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with h | h
    · subst h
      refine ⟨?_, by simp⟩
      rcases hop with h1 | h1 <;> simp [h1]
    · exact hmono g h
  · have : x6.gates.length ≤ x2 := hsize
    show (⟨x5, [x3.val, x4.val]⟩ :: x6.gates).length ≤ x2 + 1
    simp only [List.length_cons]
    omega
  · intro x11
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
    simp only [List.foldl_cons, List.map_cons, List.map_nil,
      PEqualNP.Outside.L_meta_2569.ofFn_getD]
