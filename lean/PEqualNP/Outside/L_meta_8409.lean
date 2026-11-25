import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8409

open PEqualNP.CircuitLowerBounds

theorem sim (f : ℕ → ℕ) : ∀ (gs : List Gate) (V W : List Bool),
    (∀ k, f (V.length + k) = W.length + k) →
    (∀ i < V.length, f i < W.length) →
    (∀ i < V.length, W.getD (f i) false = V.getD i false) →
    (∀ j (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < V.length + j) →
    ∀ i < V.length + gs.length,
      (List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W
          (gs.map fun g => (⟨g.op, g.inputs.map f⟩ : Gate))).getD (f i) false =
      (List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) V gs).getD
          i false := by
  intro gs
  induction gs with
  | nil =>
    intro V W _ _ hval _ i hi
    simpa using hval i (by simpa using hi)
  | cons g gs ih =>
    intro V W hf hfb hval hrb i hi
    simp only [List.map_cons, List.foldl_cons]
    have hin : ∀ i ∈ g.inputs, i < V.length := by
      intro i hi
      have := hrb 0 (by simp) i (by simpa using hi)
      simpa using this
    have heq : (g.inputs.map f).map (fun i => W.getD i false) =
        g.inputs.map (fun i => V.getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      exact hval i (hin i hi)
    have hf0 : f V.length = W.length := by simpa using hf 0
    apply ih
    · intro k
      have := hf (k + 1)
      simp only [List.length_append, List.length_singleton]
      rw [show V.length + 1 + k = V.length + (k + 1) by omega, this]
      omega
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      rcases Nat.lt_or_ge i V.length with h | h
      · have := hfb i h
        omega
      · have : i = V.length := by omega
        subst this
        omega
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      rcases Nat.lt_or_ge i V.length with h | h
      · rw [List.getD_append _ _ _ _ (hfb i h), List.getD_append _ _ _ _ h]
        exact hval i h
      · have : i = V.length := by omega
        subst this
        rw [hf0, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self,
          List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
        simp only [List.getD_cons_zero]
        exact congrArg (GateOp.eval g.op) heq
    · intro j hj i hi
      have := hrb (j + 1) (by simp; omega) i (by simpa using hi)
      simp only [List.length_append, List.length_singleton]
      omega
    · simp only [List.length_append, List.length_singleton]
      simp only [List.length_cons] at hi
      omega

theorem pre : ∀ (gs : List Gate) (W P : List Bool),
    (∀ g ∈ gs, ∀ i ∈ g.inputs, i < W.length) →
    List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (W ++ P) gs =
      W ++ P ++ gs.map (fun g => g.op.eval (g.inputs.map fun i => W.getD i false)) := by
  intro gs
  induction gs with
  | nil => intro W P _; simp
  | cons g gs ih =>
    intro W P h
    simp only [List.foldl_cons, List.map_cons]
    have he : g.inputs.map (fun i => (W ++ P).getD i false) =
        g.inputs.map (fun i => W.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact List.getD_append _ _ _ _ (h g (by simp) i hi)
    rw [he, List.append_assoc, ih W (P ++ _) (fun g' hg' => h g' (by simp [hg']))]
    simp

end PEqualNP.Outside.L_meta_8409

theorem PEqualNP.Outside.L_meta_8409 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x2 → Fin x1 × Fin x1) (x5 : Fin x3 → Fin (x1 + x2)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x3 x6 → x6.output < x3 + x6.size → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x10 ∧ x10.output < x1 + x10.size ∧ x10.size ≤ x2 + x6.size ∧ ∀ (x11 : Fin x1 → Bool), x10.eval (List.ofFn x11) = x6.eval (List.ofFn fun (x12 : Fin x3) => Fin.addCases x11 (fun (x13 : Fin x2) => x11 (x4 x13).1 || x11 (x4 x13).2) (x5 x12)) := by
  intro x1 x2 x3 x4 x5 x6 hm hrb hout
  let f : ℕ → ℕ := fun i => if h : i < x3 then (x5 ⟨i, h⟩).val else x1 + x2 + (i - x3)
  let ors : List PEqualNP.CircuitLowerBounds.Gate := List.ofFn (fun k : Fin x2 =>
    (⟨PEqualNP.CircuitLowerBounds.GateOp.or, [(x4 k).1.val, (x4 k).2.val]⟩ :
      PEqualNP.CircuitLowerBounds.Gate))
  have hf1 : ∀ i (h : i < x3), f i = (x5 ⟨i, h⟩).val := fun i h => by simp [f, h]
  have hf2 : ∀ i, x3 ≤ i → f i = x1 + x2 + (i - x3) := fun i h => by
    simp [f, show ¬ i < x3 by omega]
  have hors : ors.length = x2 := by simp [ors]
  refine ⟨⟨ors ++ x6.gates.map (fun g => (⟨g.op, g.inputs.map f⟩ : PEqualNP.CircuitLowerBounds.Gate)),
    f x6.output⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g', hg', rfl⟩
    · simp only [ors, List.mem_ofFn] at hg
      obtain ⟨k, rfl⟩ := hg
      simp
    · simpa using hm g' hg'
  · intro j hj i hi
    simp only [List.length_append, List.length_map, hors] at hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    rw [List.getD_eq_getElem _ _ (by simp [hors]; omega)] at hi
    rcases Nat.lt_or_ge j x2 with h | h
    · rw [List.getElem_append_left (by rw [hors]; exact h)] at hi
      simp only [ors, List.getElem_ofFn, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · have := (x4 ⟨j, h⟩).1.isLt
        omega
      · have := (x4 ⟨j, h⟩).2.isLt
        omega
    · rw [List.getElem_append_right (by rw [hors]; exact h)] at hi
      simp only [List.getElem_map, List.mem_map, hors] at hi
      obtain ⟨i0, hi0, rfl⟩ := hi
      have hj2 : j - x2 < x6.gates.length := by
        simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hout
        omega
      have := hrb (j - x2) hj2 i0 (by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem _ _ hj2]
        exact hi0)
      rcases Nat.lt_or_ge i0 x3 with h3 | h3
      · rw [hf1 i0 h3]
        have := (x5 ⟨i0, h3⟩).isLt
        omega
      · rw [hf2 i0 h3]
        omega
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append, List.length_map,
      hors] at hout ⊢
    rcases Nat.lt_or_ge x6.output x3 with h3 | h3
    · rw [hf1 _ h3]
      have := (x5 ⟨_, h3⟩).isLt
      omega
    · rw [hf2 _ h3]
      omega
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, hors]
  · intro x11
    let W0 : List Bool := List.ofFn x11 ++ ors.map (fun g => g.op.eval
      (g.inputs.map fun i => (List.ofFn x11).getD i false))
    have hW0e : List.foldl (fun w (g : PEqualNP.CircuitLowerBounds.Gate) =>
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x11) ors = W0 := by
      have := PEqualNP.Outside.L_meta_8409.pre ors (List.ofFn x11) [] (by
        intro g hg i hi
        simp only [ors, List.mem_ofFn] at hg
        obtain ⟨k, rfl⟩ := hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> simp)
      simpa [W0] using this
    have hW0len : W0.length = x1 + x2 := by simp [W0, hors]
    have hW0 : ∀ j : Fin (x1 + x2), W0.getD j.val false =
        Fin.addCases x11 (fun (x13 : Fin x2) => x11 (x4 x13).1 || x11 (x4 x13).2) j := by
      intro j
      refine Fin.addCases (fun a => ?_) (fun b => ?_) j
      · rw [Fin.addCases_left]
        simp only [Fin.val_castAdd, W0]
        rw [List.getD_append _ _ _ _ (by simp)]
        simp
      · rw [Fin.addCases_right]
        simp only [Fin.val_natAdd, W0]
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp [ors, PEqualNP.CircuitLowerBounds.GateOp.eval]
    let V0 : List Bool := List.ofFn fun (x12 : Fin x3) =>
      Fin.addCases x11 (fun (x13 : Fin x2) => x11 (x4 x13).1 || x11 (x4 x13).2) (x5 x12)
    have hV0len : V0.length = x3 := by simp [V0]
    show (PEqualNP.CircuitLowerBounds.Circuit.wires _ (List.ofFn x11)).getD (f x6.output) false =
      (PEqualNP.CircuitLowerBounds.Circuit.wires x6 V0).getD x6.output false
    unfold PEqualNP.CircuitLowerBounds.Circuit.wires
    simp only []
    rw [List.foldl_append, hW0e]
    apply PEqualNP.Outside.L_meta_8409.sim f x6.gates V0 W0
    · intro k
      rw [hV0len, hW0len, hf2 _ (by omega)]
      omega
    · intro i hi
      rw [hV0len] at hi
      rw [hf1 i hi, hW0len]
      exact (x5 ⟨i, hi⟩).isLt
    · intro i hi
      rw [hV0len] at hi
      rw [hf1 i hi, hW0 (x5 ⟨i, hi⟩)]
      simp only [V0]
      rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]
    · intro j hj i hi
      rw [hV0len]
      have := hrb j hj i (by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem _ _ hj]
        exact hi)
      exact this
    · rw [hV0len]
      simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hout
