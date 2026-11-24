import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1742

lemma pairCons (x y : Fin 7 → Bool) (a b : ℕ) (ha : a < 7) (hb : b < 7) (es : List (ℕ × ℕ)) :
    (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ (a, b) :: es ∧ x p = true ∧ y l = true) ↔
    (x ⟨a, ha⟩ = true ∧ y ⟨b, hb⟩ = true) ∨
      ∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ es ∧ x p = true ∧ y l = true := by
  constructor
  · rintro ⟨u, v, h, hu, hv⟩
    rcases List.mem_cons.mp h with h | h
    · obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact Or.inl ⟨(show u = ⟨a, ha⟩ from Fin.ext h1) ▸ hu, (show v = ⟨b, hb⟩ from Fin.ext h2) ▸ hv⟩
    · exact Or.inr ⟨u, v, h, hu, hv⟩
  · rintro (⟨h1, h2⟩ | ⟨u, v, h, hu, hv⟩)
    · exact ⟨⟨a, ha⟩, ⟨b, hb⟩, List.mem_cons_self, h1, h2⟩
    · exact ⟨u, v, List.mem_cons_of_mem _ h, hu, hv⟩

end PEqualNP.Outside.L_meta_1742

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_1742 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [31, 28] }], output := 32 } : PEqualNP.CircuitLowerBounds.Circuit) →
  let B2 : List (ℕ × ℕ) := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 4), (3, 5), (3, 6),
    (4, 3), (4, 5), (4, 6), (5, 3), (5, 4), (5, 6), (6, 3), (6, 4), (6, 5)];
  (∀ m : Fin 7, ((Finset.univ : Finset (Fin 7)).filter (fun p : Fin 7 => ((p : ℕ), (m : ℕ)) ∈ B2)).card = 3) ∧
  (∀ p : Fin 7, ((Finset.univ : Finset (Fin 7)).filter (fun l : Fin 7 => ((p : ℕ), (l : ℕ)) ∈ B2)).card = 3) ∧
  (∀ p p' : Fin 7, p ≠ p' → ((Finset.univ : Finset (Fin 7)).filter (fun l : Fin 7 => ((p : ℕ), (l : ℕ)) ∈ B2 ∧ ((p' : ℕ), (l : ℕ)) ∈ B2)).card ≠ 1) ∧
  C.gates.length = 19 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (7 + 7) C ∧
  (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
  ∀ (x y : Fin 7 → Bool), C.eval (List.ofFn x ++ List.ofFn y)
     = decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ B2 ∧ x p = true ∧ y l = true) := by
  rintro C rfl
  dsimp only
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, rfl, by decide +kernel, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro x y
    have hx : List.ofFn x = [x ⟨0, by decide⟩, x ⟨1, by decide⟩, x ⟨2, by decide⟩, x ⟨3, by decide⟩, x ⟨4, by decide⟩, x ⟨5, by decide⟩, x ⟨6, by decide⟩] := rfl
    have hy : List.ofFn y = [y ⟨0, by decide⟩, y ⟨1, by decide⟩, y ⟨2, by decide⟩, y ⟨3, by decide⟩, y ⟨4, by decide⟩, y ⟨5, by decide⟩, y ⟨6, by decide⟩] := rfl
    rw [hx, hy]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 0 0 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 0 1 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 0 2 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 1 0 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 1 1 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 1 2 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 2 0 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 2 1 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 2 2 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 3 4 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 3 5 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 3 6 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 4 3 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 4 5 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 4 6 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 5 3 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 5 4 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 5 6 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 6 3 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 6 4 (by decide) (by decide)]
    rw [PEqualNP.Outside.L_meta_1742.pairCons x y 6 5 (by decide) (by decide)]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, List.foldl_nil,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id_eq, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Bool.or_false, Bool.and_true,
      List.not_mem_nil, false_and, exists_false, or_false,
      Bool.or_eq_true_iff, Bool.and_eq_true_iff]
    simp only [and_or_left, or_and_right]
    apply Iff.of_eq
    ac_rfl
