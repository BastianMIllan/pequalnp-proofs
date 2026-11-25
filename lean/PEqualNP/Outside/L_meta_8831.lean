import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8831

open PEqualNP.CircuitLowerBounds

theorem fold_eq (gs : List Gate) (w : List Bool) : ∃ t : List Bool,
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t ∧
      t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, ?_⟩
    · rw [List.foldl_cons, ht]; simp
    · simp [hl]

theorem wires_eq (C : Circuit) (x : List Bool) : ∃ t : List Bool,
    C.wires x = x ++ t ∧ t.length = C.gates.length := by
  unfold Circuit.wires
  exact fold_eq C.gates x

end PEqualNP.Outside.L_meta_8831

theorem PEqualNP.Outside.L_meta_8831 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → x1 ≤ x4.output ∧ x4.output < x1 + x4.size := by
  intro x1 x2 x3 x4 hf hex
  obtain ⟨u, v, huv⟩ := hex
  have hfx : ∀ y : Fin x1 → Bool, x4.eval (List.ofFn y) =
      PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ y := fun y => congrFun hf y
  constructor
  · by_contra h
    push Not at h
    let y : Fin x1 → Bool := fun w => decide (w = ⟨x4.output, h⟩)
    have h1 : x4.eval (List.ofFn y) = true := by
      obtain ⟨t, ht, _⟩ := PEqualNP.Outside.L_meta_8831.wires_eq x4 (List.ofFn y)
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      rw [ht, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h)]
      simp [y, h]
    have h2 : PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ y = false := by
      simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, y]
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      refine ⟨by simp, ?_⟩
      rintro ⟨a, b, hab, ha, hb⟩
      simp only [decide_eq_true_eq] at ha hb
      subst ha
      subst hb
      exact x2.irrefl hab
    rw [hfx, h2] at h1
    simp at h1
  · by_contra h
    push Not at h
    let y : Fin x1 → Bool := fun w => decide (w = u ∨ w = v)
    have h1 : x4.eval (List.ofFn y) = false := by
      obtain ⟨t, ht, hl⟩ := PEqualNP.Outside.L_meta_8831.wires_eq x4 (List.ofFn y)
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
      · rfl
      · rw [ht]
        simp only [List.length_append, List.length_ofFn, hl]
        simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using h
    have h2 : PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ y = true := by
      simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_true,
        decide_eq_true_eq]
      right
      exact ⟨u, v, huv, by simp [y], by simp [y]⟩
    rw [hfx, h2] at h1
    simp at h1
