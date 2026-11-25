import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6848

open PEqualNP.CircuitLowerBounds

def wf (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  if h : i < n then (σ ⟨i, h⟩).val else i

theorem wf_lt (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : ℕ) (h : i < n) : wf n σ i < n := by
  unfold wf; rw [dif_pos h]; exact (σ ⟨i, h⟩).isLt

theorem wf_ge (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : ℕ) (h : n ≤ i) : wf n σ i = i := by
  unfold wf; rw [dif_neg (by omega)]

def mapG (n : ℕ) (σ : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wf n σ)⟩

theorem key {α : Type} (n : ℕ) (σ : Equiv.Perm (Fin n)) (dflt : α) (S : Gate → List α → α)
    (hS : ∀ g A B, (∀ i, A.getD (wf n σ i) dflt = B.getD i dflt) → S (mapG n σ g) A = S g B) :
    ∀ (G : List Gate) (A B : List α), A.length = B.length → n ≤ A.length →
      (∀ i, A.getD (wf n σ i) dflt = B.getD i dflt) →
      ∀ i, (List.foldl (fun d g => d ++ [S g d]) A (G.map (mapG n σ))).getD (wf n σ i) dflt =
        (List.foldl (fun d g => d ++ [S g d]) B G).getD i dflt := by
  intro G
  induction G with
  | nil => intro A B _ _ h i; exact h i
  | cons g G ih =>
    intro A B hl hn h
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [hl]
    · simp; omega
    · intro i
      have hv := hS g A B h
      by_cases hi : i < n
      · have h1 := wf_lt n σ i hi
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact h i
      · have h2 := wf_ge n σ i (by omega)
        rw [h2]
        rcases Nat.lt_trichotomy i A.length with h3 | h3 | h3
        · rw [List.getD_append _ _ _ _ h3, List.getD_append _ _ _ _ (by omega)]
          have := h i; rw [h2] at this; exact this
        · subst h3
          rw [List.getD_append_right _ _ _ _ (le_refl _), List.getD_append_right _ _ _ _ (by omega)]
          simp [hl, hv]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem filt (n : ℕ) (σ : Equiv.Perm (Fin n)) (l : List ℕ) :
    (l.map (wf n σ)).filter (fun x => decide (n ≤ x)) = l.filter (fun x => decide (n ≤ x)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : n ≤ a
    · rw [List.map_cons, wf_ge n σ a ha, List.filter_cons_of_pos (by simpa using ha),
        List.filter_cons_of_pos (by simpa using ha), ih]
    · have := wf_lt n σ a (by omega)
      rw [List.map_cons, List.filter_cons_of_neg (by simp; omega),
        List.filter_cons_of_neg (by simp; omega), ih]

theorem flat (n : ℕ) (σ : Equiv.Perm (Fin n)) (G : List Gate) :
    (G.map (mapG n σ)).flatMap Gate.inputs = (G.flatMap Gate.inputs).map (wf n σ) := by
  induction G with
  | nil => rfl
  | cons g G ih => simp [List.flatMap_cons, ih, mapG]

theorem main (C : Circuit) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ∃ (D : Circuit), D.size = C.size ∧ (∀ (j : ℕ) (g : Gate), D.gates[j]? = Option.some g → ∃ (h : Gate), C.gates[j]? = Option.some h ∧ g.op = h.op ∧ g.inputs = List.map (wf n σ) h.inputs) ∧ List.filter (fun (x6 : ℕ) => Decidable.decide (n ≤ x6)) (D.output :: List.flatMap Gate.inputs D.gates) = List.filter (fun (x6 : ℕ) => Decidable.decide (n ≤ x6)) (C.output :: List.flatMap Gate.inputs C.gates) ∧ (∀ (i : Fin n), D.lineDeg n {↑(σ i)} = C.lineDeg n {↑i}) ∧ (PEqualNP.MetaComplexity.SingleLevel.andDepths D n).getD D.output (0 : ℕ) = (PEqualNP.MetaComplexity.SingleLevel.andDepths C n).getD C.output (0 : ℕ) ∧ ∀ (x : Fin n → Bool), D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ ⇑σ)) := by
  refine ⟨⟨C.gates.map (mapG n σ), wf n σ C.output⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Circuit.size]
  · intro j g hg
    simp only [List.getElem?_map] at hg
    cases hc : C.gates[j]? with
    | none => rw [hc] at hg; simp at hg
    | some h =>
      rw [hc] at hg
      simp only [Option.map_some, Option.some.injEq] at hg
      subst hg
      exact ⟨h, rfl, rfl, rfl⟩
  · show List.filter _ (wf n σ C.output :: List.flatMap Gate.inputs (C.gates.map (mapG n σ))) = _
    rw [flat]
    have := filt n σ (C.output :: List.flatMap Gate.inputs C.gates)
    simpa using this
  · intro i0
    unfold Circuit.lineDeg Circuit.lineDegrees
    apply key n σ 0 (fun g d => g.lineDegree d)
    · intro g A B h
      have hv : (mapG n σ g).inputs.map (fun i => A.getD i 0) = g.inputs.map (fun i => B.getD i 0) := by
        simp only [mapG, List.map_map]
        apply List.map_congr_left
        intro i _
        exact h i
      unfold Gate.lineDegree
      rw [hv]
      rfl
    · simp
    · simp
    · intro i
      by_cases hi : i < n
      · have h1 := wf_lt n σ i hi
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h1, hi,
          if_true, Option.map_some, Option.getD_some, Finset.mem_singleton]
        have e : wf n σ i = (σ ⟨i, hi⟩).val := by unfold wf; rw [dif_pos hi]
        rw [e]
        have : ((σ ⟨i, hi⟩).val = (σ i0).val) ↔ (i = i0.val) := by
          constructor
          · intro hh
            have := σ.injective (Fin.ext hh)
            rw [← this]
          · intro hh
            have : (⟨i, hi⟩ : Fin n) = i0 := Fin.ext hh
            rw [this]
        by_cases hh : i = i0.val
        · rw [if_pos (this.2 hh), if_pos hh]
        · rw [if_neg (fun e => hh (this.1 e)), if_neg hh]
      · rw [wf_ge n σ i (by omega)]
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  · unfold PEqualNP.MetaComplexity.SingleLevel.andDepths
    apply key n σ 0 (fun g d => (g.inputs.map fun i => d.getD i 0).foldr max 0 + PEqualNP.MetaComplexity.SingleLevel.andLevel g)
    · intro g A B h
      have hv : (mapG n σ g).inputs.map (fun i => A.getD i 0) = g.inputs.map (fun i => B.getD i 0) := by
        simp only [mapG, List.map_map]
        apply List.map_congr_left
        intro i _
        exact h i
      have hl : PEqualNP.MetaComplexity.SingleLevel.andLevel (mapG n σ g) = PEqualNP.MetaComplexity.SingleLevel.andLevel g := by
        obtain ⟨op, ins⟩ := g
        unfold PEqualNP.MetaComplexity.SingleLevel.andLevel mapG
        rcases ins with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> cases op <;> rfl
      show List.foldr max 0 ((mapG n σ g).inputs.map fun i => A.getD i 0) + _ = _
      rw [hv, hl]
    · simp
    · simp
    · intro i
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> split <;> rfl
  · intro x
    unfold Circuit.eval Circuit.wires
    apply key n σ false (fun g w => g.op.eval (g.inputs.map fun i => w.getD i false))
    · intro g A B h
      have hv : (mapG n σ g).inputs.map (fun i => A.getD i false) = g.inputs.map (fun i => B.getD i false) := by
        simp only [mapG, List.map_map]
        apply List.map_congr_left
        intro i _
        exact h i
      show GateOp.eval (mapG n σ g).op _ = _
      rw [hv]
      rfl
    · simp
    · simp
    · intro i
      by_cases hi : i < n
      · have h1 := wf_lt n σ i hi
        have e : wf n σ i = (σ ⟨i, hi⟩).val := by unfold wf; rw [dif_pos hi]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, e, Function.comp]
        simp [hi, (σ ⟨i, hi⟩).isLt]
      · rw [wf_ge n σ i (by omega)]
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_6848

open PEqualNP.Outside.L_meta_6848 in
theorem PEqualNP.Outside.L_meta_6848 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Equiv.Perm (Fin x2)),   have x4 : ℕ → ℕ := fun (x4 : ℕ) => if x5 : x4 < x2 then ↑(x3 (⟨x4, x5⟩ : Fin x2)) else x4;   ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x5.size = x1.size ∧ (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x6]? = Option.some x7 → ∃ (x9 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x9 ∧ x7.op = x9.op ∧ x7.inputs = List.map x4 x9.inputs) ∧ List.filter (fun (x6 : ℕ) => Decidable.decide (x2 ≤ x6)) (x5.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x5.gates) = List.filter (fun (x6 : ℕ) => Decidable.decide (x2 ≤ x6)) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates) ∧ (∀ (x6 : Fin x2), x5.lineDeg x2 {↑(x3 x6)} = x1.lineDeg x2 {↑x6}) ∧ (PEqualNP.MetaComplexity.SingleLevel.andDepths x5 x2).getD x5.output (0 : ℕ) = (PEqualNP.MetaComplexity.SingleLevel.andDepths x1 x2).getD x1.output (0 : ℕ) ∧ ∀ (x6 : Fin x2 → Bool), x5.eval (List.ofFn x6) = x1.eval (List.ofFn (x6 ∘ ⇑x3)) := by
  intro x1 x2 x3
  exact main x1 x2 x3
