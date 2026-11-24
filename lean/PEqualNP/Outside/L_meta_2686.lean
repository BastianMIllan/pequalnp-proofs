import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2686

open PEqualNP.CircuitLowerBounds

def C0 : Circuit :=
  ⟨[(⟨GateOp.or, [0, 1]⟩ : Gate), ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [5, 9]⟩], 10⟩

theorem tab : ∀ a b c d e : Bool,
    C0.eval (List.ofFn ![a, b, c, d, e]) =
      ((a && b) || (a && c) || (a && d) || (b && c) || (b && e)) := by
  decide

theorem fn (x : Fin 5 → Bool) :
    PEqualNP.MetaComplexity.circuitFun 5 C0 x =
      ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) := by
  have h := tab (x 0) (x 1) (x 2) (x 3) (x 4)
  have hx : ![x 0, x 1, x 2, x 3, x 4] = x := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at h
  exact h

theorem ao2 : PEqualNP.TopForm.IsAO2 5 C0 := by decide

theorem w1 : ∀ t ∈ [0, 1, 3, 4, 2, 8], ∃ x : Fin 5 → Bool,
    (C0.wires (List.ofFn x)).getD t false = true ∧
      PEqualNP.MetaComplexity.circuitFun 5 C0 x = false := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨![true, false, false, false, false], by decide⟩
  · exact ⟨![false, true, false, false, false], by decide⟩
  · exact ⟨![false, false, false, true, false], by decide⟩
  · exact ⟨![false, false, false, false, true], by decide⟩
  · exact ⟨![false, false, true, false, false], by decide⟩
  · exact ⟨![false, false, false, true, true], by decide⟩

theorem w2 : ∀ t ∈ [5, 6, 7, 8, 9], ∃ x : Fin 5 → Bool,
    (C0.wires (List.ofFn x)).getD t false = true ∧
      PEqualNP.MetaComplexity.circuitFun 5 C0 x = false := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact ⟨![true, false, false, false, false], by decide⟩
  · exact ⟨![false, true, false, false, false], by decide⟩
  · exact ⟨![true, false, false, false, false], by decide⟩
  · exact ⟨![false, false, false, true, true], by decide⟩
  · exact ⟨![false, false, true, false, false], by decide⟩

end PEqualNP.Outside.L_meta_2686

theorem PEqualNP.Outside.L_meta_2686 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ⟨[(⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ : PEqualNP.CircuitLowerBounds.Gate), ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 9]⟩], 10⟩ → C.gates.length = 6 ∧ PEqualNP.TopForm.IsAO2 5 C ∧ (∀ x : Fin 5 → Bool, PEqualNP.MetaComplexity.circuitFun 5 C x = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4))) ∧ (∀ t ∈ [0, 1, 3, 4, 2, 8], ∃ x : Fin 5 → Bool, (C.wires (List.ofFn x)).getD t false = true ∧ PEqualNP.MetaComplexity.circuitFun 5 C x = false) ∧ (∀ t ∈ [5, 6, 7, 8, 9], ∃ x : Fin 5 → Bool, (C.wires (List.ofFn x)).getD t false = true ∧ PEqualNP.MetaComplexity.circuitFun 5 C x = false) := by
  intro C hC
  subst hC
  exact ⟨rfl, PEqualNP.Outside.L_meta_2686.ao2, PEqualNP.Outside.L_meta_2686.fn,
    PEqualNP.Outside.L_meta_2686.w1, PEqualNP.Outside.L_meta_2686.w2⟩
