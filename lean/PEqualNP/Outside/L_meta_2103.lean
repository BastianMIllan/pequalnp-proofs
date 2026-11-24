import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2103

open PEqualNP.CircuitLowerBounds

-- The OR of a relabelled circuit and a second circuit: the second circuit first, then the
-- relabelled gates of the first, then one OR gate reading the two outputs (when they exist).

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_nil (w : List Bool) : wf [] w = w := rfl

theorem wf_append (gs gs' : List Gate) (w : List Bool) :
    wf (gs ++ gs') w = wf gs' (wf gs w) := by
  simp [wf, List.foldl_append]

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_prefix (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, wf gs w = w ++ t ∧ t.length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨[], by simp [wf_nil], rfl⟩
  | append_singleton gs g ih =>
    obtain ⟨t, ht, hl⟩ := ih
    refine ⟨t ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)], ?_, by simp [hl]⟩
    rw [wf_snoc, ht]; simp

theorem wf_length (gs : List Gate) (w : List Bool) : (wf gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wf_prefix gs w
  rw [ht]; simp [hl]

theorem wf_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (wf gs w).getD k false = w.getD k false := by
  obtain ⟨t, ht, _⟩ := wf_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hk]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def relabel (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem relabel_wf (A B : List Bool) (f : ℕ → ℕ)
    (hf0 : ∀ i < A.length, f i < B.length)
    (hf1 : ∀ i < A.length, B.getD (f i) false = A.getD i false)
    (hf2 : ∀ i, A.length ≤ i → f i = B.length + (i - A.length)) :
    ∀ gs : List Gate, (∀ j (h : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < A.length + j) →
    ∀ i < A.length + gs.length,
      (wf (gs.map (relabel f)) B).getD (f i) false = (wf gs A).getD i false := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ i hi
    simp only [List.length_nil, add_zero] at hi
    simp only [List.map_nil, wf_nil]
    exact hf1 i hi
  | append_singleton gs g ih =>
    intro hr i hi
    have hr' : ∀ j (h : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < A.length + j := by
      intro j h i hi
      exact hr j (by simp; omega) i (by rw [List.getElem_append_left h]; exact hi)
    have ih' := ih hr'
    rw [List.map_append, List.map_singleton, wf_snoc, wf_snoc]
    have hlB : (wf (gs.map (relabel f)) B).length = B.length + gs.length := by
      rw [wf_length, List.length_map]
    have hlA : (wf gs A).length = A.length + gs.length := wf_length _ _
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hil : i < A.length + gs.length
    · have hfi : f i < B.length + gs.length := by
        by_cases h0 : i < A.length
        · have := hf0 i h0; omega
        · rw [hf2 i (by omega)]; omega
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact ih' i hil
    · have hieq : i = A.length + gs.length := by omega
      subst hieq
      have hfi : f (A.length + gs.length) = (wf (gs.map (relabel f)) B).length := by
        rw [hf2 _ (by omega), hlB]; omega
      rw [hfi, getD_snoc_eq, ← hlA, getD_snoc_eq]
      show g.op.eval ((g.inputs.map f).map fun i => (wf (gs.map (relabel f)) B).getD i false)
        = g.op.eval (g.inputs.map fun i => (wf gs A).getD i false)
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih' a (hr gs.length (by simp) a (by simp [ha]))

def fmap (x1 x2 s5 : ℕ) (x3 : Fin x1 → Fin x2) (i : ℕ) : ℕ :=
  if h : i < x1 then (x3 ⟨i, h⟩).val else x2 + s5 + (i - x1)

def orIns (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 x5 : Circuit) : List ℕ :=
  (if x4.output < x1 + x4.gates.length then [fmap x1 x2 x5.gates.length x3 x4.output] else []) ++
    (if x5.output < x2 + x5.gates.length then [x5.output] else [])

def combo (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 x5 : Circuit) : Circuit :=
  ⟨x5.gates ++ x4.gates.map (relabel (fmap x1 x2 x5.gates.length x3)) ++
      [⟨GateOp.or, orIns x1 x2 x3 x4 x5⟩],
    x2 + x5.gates.length + x4.gates.length⟩

theorem main (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 x5 : Circuit)
    (h4 : PEqualNP.MetaComplexity.Monotone2 x4)
    (hr4 : PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x4)
    (h5 : PEqualNP.MetaComplexity.Monotone2 x5) :
    ∃ (x10 : Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧
      x10.size ≤ x4.size + x5.size + (1 : ℕ) ∧
      ∀ (x11 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x10 x11 =
        ((PEqualNP.MetaComplexity.circuitFun x1 x4 fun (x12 : Fin x1) => x11 (x3 x12)) ||
          PEqualNP.MetaComplexity.circuitFun x2 x5 x11) := by
  refine ⟨combo x1 x2 x3 x4 x5, ?_, ?_, ?_⟩
  · intro g hg
    simp only [combo, List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with (hg | ⟨a, ha, rfl⟩) | rfl
    · exact h5 g hg
    · have := h4 a ha
      exact ⟨this.1, by simpa [relabel] using this.2⟩
    · refine ⟨by simp, ?_⟩
      simp only [orIns]
      split_ifs <;> simp
  · simp [combo, Circuit.size]
    omega
  · intro x11
    set s5 := x5.gates.length with hs5
    set s4 := x4.gates.length with hs4
    set f := fmap x1 x2 s5 x3 with hf
    set y : List Bool := List.ofFn x11 with hy
    set A : List Bool := List.ofFn (fun i : Fin x1 => x11 (x3 i)) with hA
    set W5 := wf x5.gates y with hW5
    set W4 := wf (x4.gates.map (relabel f)) W5 with hW4
    have hyl : y.length = x2 := by simp [hy]
    have hAl : A.length = x1 := by simp [hA]
    have hW5l : W5.length = x2 + s5 := by rw [hW5, wf_length, hyl]
    have hW4l : W4.length = x2 + s5 + s4 := by rw [hW4, wf_length, hW5l, List.length_map]
    have hrel := relabel_wf A W5 f
      (by
        intro i hi
        rw [hAl] at hi
        rw [hW5l, hf, fmap, dif_pos hi]
        have := (x3 ⟨i, hi⟩).isLt
        omega)
      (by
        intro i hi
        rw [hAl] at hi
        rw [hf, fmap, dif_pos hi, hW5, wf_getD_lt _ _ _ (by rw [hyl]; exact (x3 ⟨i, hi⟩).isLt)]
        simp [hy, hA, hi])
      (by
        intro i hi
        rw [hAl] at hi
        rw [hf, fmap, dif_neg (by omega), hW5l, hAl])
      x4.gates
      (by
        intro j h i hi
        rw [hAl]
        have := hr4 j h i
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at this
        rw [List.getD_eq_getElem _ _ h] at this
        exact this hi)
    have hwires : (combo x1 x2 x3 x4 x5).wires y = W4 ++
        [GateOp.or.eval ((orIns x1 x2 x3 x4 x5).map fun i => W4.getD i false)] := by
      show wf (x5.gates ++ x4.gates.map (relabel f) ++ [⟨GateOp.or, orIns x1 x2 x3 x4 x5⟩]) y = _
      rw [wf_snoc, wf_append]
    have e4 : x4.eval A = if x4.output < x1 + s4 then W4.getD (f x4.output) false else false := by
      show (wf x4.gates A).getD x4.output false = _
      split_ifs with ho
      · rw [hW4]; exact (hrel x4.output (by rw [hAl]; exact ho)).symm
      · rw [List.getD_eq_default _ _ (by rw [wf_length, hAl]; omega)]
    have e5 : x5.eval y = if x5.output < x2 + s5 then W4.getD x5.output false else false := by
      show W5.getD x5.output false = _
      split_ifs with ho
      · rw [hW4, wf_getD_lt (x4.gates.map (relabel f)) W5 x5.output (by rw [hW5l]; exact ho)]
      · rw [List.getD_eq_default _ _ (by rw [hW5l]; omega)]
    show (combo x1 x2 x3 x4 x5).eval y = (x4.eval A || x5.eval y)
    rw [Circuit.eval, hwires]
    have hout : (combo x1 x2 x3 x4 x5).output = W4.length := by
      rw [hW4l]; rfl
    rw [hout, getD_snoc_eq, e4, e5]
    simp only [orIns]
    split_ifs <;> simp [GateOp.eval, hf, hs5]

end PEqualNP.Outside.L_meta_2103

theorem PEqualNP.Outside.L_meta_2103 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (x4 x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x4 → PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x5 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x4.size + x5.size + (1 : ℕ) ∧ ∀ (x11 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x10 x11 = ((PEqualNP.MetaComplexity.circuitFun x1 x4 fun (x12 : Fin x1) => x11 (x3 x12)) || PEqualNP.MetaComplexity.circuitFun x2 x5 x11) := by
  intro x1 x2 x3 x4 x5 h4 hr4 h5 _
  exact PEqualNP.Outside.L_meta_2103.main x1 x2 x3 x4 x5 h4 hr4 h5
