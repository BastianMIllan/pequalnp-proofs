import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3453

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_append (L : List Gate) : ∀ w : List Bool, ∃ t, L.foldl step w = w ++ t := by
  induction L with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g L ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (step w g)
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by
      rw [List.foldl_cons, ht]; simp [step]⟩

theorem fold_length (L : List Gate) : ∀ w : List Bool, (L.foldl step w).length = w.length + L.length := by
  induction L with
  | nil => intro w; simp
  | cons g L ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem getD_app (l t : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ t).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_step (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false = if i < w.length then w.getD i false else
      if i = w.length then g.op.eval (g.inputs.map fun k => w.getD k false) else false := by
  unfold step
  split_ifs with h1 h2
  · exact getD_app _ _ _ h1
  · subst h2; simp
  · have h3 : (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).length ≤ i := by
      simp; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h3]
    rfl

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (L : List ℕ)
    (f g : ℕ → Bool) (h : ∀ i ∈ L, f i = true → g i = true) :
    op.eval (L.map f) = true → op.eval (L.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro hf b hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact h i hi (hf (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨g i, ⟨i, hi, rfl⟩, h i hi hb⟩

theorem step_congr (w : List Bool) (g : Gate) (rho : ℕ → ℕ)
    (h : ∀ k ∈ g.inputs, w.getD (rho k) false = w.getD k false) :
    step w ⟨g.op, g.inputs.map rho⟩ = step w g := by
  have e : (g.inputs.map rho).map (fun i => w.getD i false) =
      g.inputs.map (fun i => w.getD i false) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    exact h k hk
  unfold step
  dsimp only
  rw [e]

theorem take_step (L : List Gate) (X : List Bool) (j : ℕ) (hj : j < L.length) :
    (L.take (j + 1)).foldl step X = step ((L.take j).foldl step X) L[j] := by
  rw [List.take_succ_eq_append_getElem hj, List.foldl_append]
  rfl

theorem take_get (L : List Gate) (X : List Bool) (j : ℕ) (hj : j ≤ L.length) (i : ℕ)
    (hi : i < X.length + j) :
    ((L.take j).foldl step X).getD i false = (L.foldl step X).getD i false := by
  have e : L.foldl step X = (L.drop j).foldl step ((L.take j).foldl step X) := by
    conv_lhs => rw [← List.take_append_drop j L]
    rw [List.foldl_append]
  obtain ⟨t, ht⟩ := fold_append (L.drop j) ((L.take j).foldl step X)
  rw [e, ht, getD_app]
  rw [fold_length]
  simp [List.length_take]
  omega

end PEqualNP.Outside.L_meta_3453

open PEqualNP.Outside.L_meta_3453 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_3453 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ) (sigma : ℕ → ℕ) (x : Fin n → Bool), PEqualNP.TopForm.IsAO2 n C → u < C.gates.length → (∀ r : ℕ, sigma r < n + u) → ((∀ r < C.gates.length, n + u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs → (C.wires (List.ofFn x)).getD (sigma r) false = true → (C.wires (List.ofFn x)).getD (n + u) false = true) → ∀ i : ℕ, ((PEqualNP.FactorSubst.substReads C n u sigma).wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn x)).getD i false = true) ∧ ((∀ r < C.gates.length, n + u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs → (C.wires (List.ofFn x)).getD (sigma r) false = (C.wires (List.ofFn x)).getD (n + u) false) → (PEqualNP.FactorSubst.substReads C n u sigma).wires (List.ofFn x) = C.wires (List.ofFn x)) := by
  intro n C u sigma x hC hu hsig
  obtain ⟨hAO, hRB, -⟩ := hC
  have hAO' : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := hAO
  have hRB' : ∀ j < C.gates.length, ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB
  set L := C.gates with hL
  set L' := (PEqualNP.FactorSubst.substReads C n u sigma).gates with hL'
  set X := List.ofFn x with hX
  have hXl : X.length = n := by simp [hX]
  have hlen : L'.length = L.length := by simp [hL', hL, PEqualNP.FactorSubst.substReads]
  have hget : ∀ j (hj : j < L.length), L'[j]'(by omega) =
      ⟨L[j].op, L[j].inputs.map fun i => if i = n + u then sigma j else i⟩ := by
    intro j hj
    simp [hL', hL, PEqualNP.FactorSubst.substReads, List.getElem_mapIdx]
  have hga : ∀ j (hj : j < L.length), gateAt C j = L[j] := by
    intro j hj
    have hj2 : j < C.gates.length := hj
    simp only [gateAt, hL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2, Option.getD_some]
  have hW : C.wires X = L.foldl step X := rfl
  have hW' : (PEqualNP.FactorSubst.substReads C n u sigma).wires X = L'.foldl step X := rfl
  have lenQ : ∀ j ≤ L.length, ((L.take j).foldl step X).length = n + j := by
    intro j hj; rw [fold_length]; simp [List.length_take]; omega
  have lenP : ∀ j ≤ L.length, ((L'.take j).foldl step X).length = n + j := by
    intro j hj; rw [fold_length]; simp [List.length_take]; omega
  refine ⟨?_, ?_⟩
  · intro hyp
    have main : ∀ j ≤ L.length, ∀ i, ((L'.take j).foldl step X).getD i false = true →
        ((L.take j).foldl step X).getD i false = true := by
      intro j
      induction j with
      | zero => intro _ i h; simpa using h
      | succ j ih =>
        intro hj i hi
        have hj' : j < L.length := hj
        have ih' := ih hj'.le
        rw [take_step L X j hj']
        rw [take_step L' X j (by omega), getD_step] at hi
        rw [getD_step]
        rw [lenP j hj'.le] at hi
        rw [lenQ j hj'.le]
        split_ifs at hi ⊢ with h1 h2
        · exact ih' i hi
        · rw [hget j hj'] at hi
          simp only [List.map_map] at hi
          refine eval_mono _ (hAO' _ (List.getElem_mem hj')) _ _ _ ?_ hi
          intro k hk hk2
          simp only [Function.comp] at hk2
          have hkr : k < n + j := by
            have := hRB' j hj' k (by rw [hga j hj']; exact hk)
            exact this
          by_cases hku : k = n + u
          · rw [if_pos hku] at hk2
            have s1 := ih' _ hk2
            have hsl : sigma j < n + j := by have := hsig j; omega
            rw [take_get L X j hj'.le _ (by omega)] at s1
            have s2 := hyp j hj' (by rw [hga j hj']; rw [← hku]; exact hk) s1
            rw [hku, take_get L X j hj'.le _ (by omega)]
            exact s2
          · rw [if_neg hku] at hk2
            exact ih' k hk2
    intro i hi
    rw [hW] at *
    rw [hW'] at hi
    have := main L.length le_rfl i
    rw [List.take_length, ← hlen, List.take_length] at this
    exact this hi
  · intro hyp
    have main : ∀ j ≤ L.length, (L'.take j).foldl step X = (L.take j).foldl step X := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ih =>
        intro hj
        have hj' : j < L.length := hj
        rw [take_step L X j hj', take_step L' X j (by omega), ih hj'.le, hget j hj']
        apply step_congr
        intro k hk
        by_cases hku : k = n + u
        · rw [if_pos hku]
          have hkr : k < n + j := by
            have := hRB' j hj' k (by rw [hga j hj']; exact hk)
            exact this
          have hsl : sigma j < n + j := by have := hsig j; omega
          rw [take_get L X j hj'.le _ (by omega), take_get L X j hj'.le _ (by omega)]
          have e3 := hyp j hj' (by rw [hga j hj']; rw [← hku]; exact hk)
          rw [hW] at e3
          rw [e3, hku]
        · rw [if_neg hku]
    rw [hW, hW']
    have := main L.length le_rfl
    rw [List.take_length, ← hlen, List.take_length] at this
    exact this
