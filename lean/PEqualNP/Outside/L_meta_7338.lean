import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7338

open PEqualNP.CircuitLowerBounds

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_init2 (n : ℕ) (π : Fin n → Fin n) (x : Fin n → Bool) (t : List Bool) :
    Rel n n π (List.ofFn (x ∘ π) ++ t) (List.ofFn x ++ t) := by
  refine ⟨by simp, by simp, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    have h1 : ((π ⟨w, hw⟩ : Fin n) : ℕ) < (List.ofFn x).length := by simp
    have h2 : w < (List.ofFn (x ∘ π)).length := by simpa using hw
    rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2,
      List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
    simp
  · rename_i hw
    have h1 : (List.ofFn x).length ≤ w - n + n := by simp
    have h2 : (List.ofFn (x ∘ π)).length ≤ w := by simp; omega
    rw [List.getD_append_right _ _ _ _ h1, List.getD_append_right _ _ _ _ h2]
    simp

lemma fan (n : ℕ) (π : Fin n → Fin n) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (relabel n n π C) := by
  intro g hg
  simp only [relabel, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  obtain ⟨a, b⟩ := h g0 hg0
  exact ⟨a, by simpa [relGate] using b⟩

end PEqualNP.Outside.L_meta_7338

theorem PEqualNP.Outside.L_meta_7338 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1 → Fin x1), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x2.size ∧ ∀ (x6 : Fin x1 → Bool) (x7 : List Bool), x5.eval (List.ofFn x6 ++ x7) = x2.eval (List.ofFn (x6 ∘ x3) ++ x7) := by
  intro x1 x2 x3 hf
  refine ⟨PEqualNP.Outside.L_meta_7338.relabel x1 x1 x3 x2,
    PEqualNP.Outside.L_meta_7338.fan x1 x3 x2 hf, ?_, ?_⟩
  · simp [PEqualNP.Outside.L_meta_7338.relabel, PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x6 x7
    have h := (PEqualNP.Outside.L_meta_7338.rel_fold x1 x1 x3 x2.gates _ _
      (PEqualNP.Outside.L_meta_7338.rel_init2 x1 x3 x6 x7)).2.2 x2.output
    exact h
