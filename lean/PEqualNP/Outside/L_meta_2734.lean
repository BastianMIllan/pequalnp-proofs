import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2734

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

end PEqualNP.Outside.L_meta_2734

theorem PEqualNP.Outside.L_meta_2734 : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x1) (x5 x6 : Fin (x1 + (1 : ℕ))) (x7 x8 : PEqualNP.CircuitLowerBounds.GateOp),   x7 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x7 = PEqualNP.CircuitLowerBounds.GateOp.or →     x8 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x8 = PEqualNP.CircuitLowerBounds.GateOp.or →       ∀ (x11 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.Monotone2 x11 →           x11.size ≤ x2 →             ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit),               PEqualNP.MetaComplexity.Monotone2 x14 ∧                 x14.size ≤ x2 + (2 : ℕ) ∧                   ∀ (x15 : Fin x1 → Bool),                     have x16 : List Bool := List.ofFn x15 ++ [x7.eval [x15 x3, x15 x4]];                     x14.eval (List.ofFn x15) = x11.eval (x16 ++ [x8.eval [x16.getD (↑x5) Bool.false, x16.getD (↑x6) Bool.false]]) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 h7 h8 x11 hm hs
  refine ⟨⟨⟨x7, [(x3 : ℕ), (x4 : ℕ)]⟩ :: ⟨x8, [(x5 : ℕ), (x6 : ℕ)]⟩ :: x11.gates, x11.output⟩,
    ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · refine ⟨?_, by simp⟩
      rcases h7 with h | h <;> simp [h]
    · refine ⟨?_, by simp⟩
      rcases h8 with h | h <;> simp [h]
    · exact hm g hg
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_cons] at hs ⊢
    omega
  · intro x15
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl_cons, List.map_cons, List.map_nil,
      PEqualNP.Outside.L_meta_2734.getD_ofFn]
