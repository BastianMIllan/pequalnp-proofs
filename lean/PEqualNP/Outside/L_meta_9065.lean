import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9065

open PEqualNP.CircuitLowerBounds

def Le (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, w.getD i false = true → w'.getD i false = true

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem op_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f g : ℕ → Bool) (h : ∀ i, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i h1⟩

theorem getD_snoc (w : List Bool) (a : Bool) (i : ℕ) :
    (w ++ [a]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then a else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [if_pos h, List.getElem?_append_left h]
  · rw [if_neg h]
    by_cases h2 : i = w.length
    · subst h2; simp
    · rw [if_neg h2]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl

theorem snoc_le (w w' : List Bool) (a b : Bool) (hw : Le w w') (hab : a = true → b = true) :
    Le (w ++ [a]) (w' ++ [b]) := by
  refine ⟨by simp [hw.1], ?_⟩
  intro i hi
  rw [getD_snoc] at hi ⊢
  rw [← hw.1]
  by_cases h : i < w.length
  · rw [if_pos h] at hi ⊢; exact hw.2 i hi
  · rw [if_neg h] at hi ⊢
    by_cases h2 : i = w.length
    · rw [if_pos h2] at hi ⊢; exact hab hi
    · rw [if_neg h2] at hi; cases hi

theorem fold_le (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w', Le w w' → Le (gs.foldl step w) (gs.foldl step w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    intro w w' h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    apply snoc_le _ _ _ _ h
    exact op_mono g.op (hg g (List.mem_cons_self ..)) g.inputs _ _ h.2

theorem eval_mono (C : Circuit) (hC : PEqualNP.EdgeOwnership.AndOrOnly C) (x y : List Bool)
    (h : Le x y) : C.eval x = true → C.eval y = true := by
  have := fold_le C.gates hC x y h
  exact this.2 C.output

theorem ofFn_le {n : ℕ} (f g : Fin n → Bool) (h : ∀ i, f i = true → g i = true) :
    Le (List.ofFn f) (List.ofFn g) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  simp only [List.getD_eq_getElem?_getD] at hi ⊢
  by_cases hn : i < n
  · simp [List.getElem?_ofFn, hn] at hi ⊢
    exact h _ hi
  · rw [List.getElem?_eq_none (by simp; omega)] at hi
    cases hi

end PEqualNP.Outside.L_meta_9065

theorem PEqualNP.Outside.L_meta_9065 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly x1 → Monotone fun (x3 : Fin (26 : ℕ) → Bool) => x1.eval (List.ofFn x3 ++ [x3 (1 : Fin (26 : ℕ)) || x3 (2 : Fin (26 : ℕ))]) := by
  intro C hC x y hxy
  have hi : ∀ i, x i = true → y i = true := fun i => Bool.le_iff_imp.mp (hxy i)
  apply Bool.le_iff_imp.mpr
  apply PEqualNP.Outside.L_meta_9065.eval_mono C hC
  apply PEqualNP.Outside.L_meta_9065.snoc_le _ _ _ _
    (PEqualNP.Outside.L_meta_9065.ofFn_le x y hi)
  intro h
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl (hi _ h)
  · exact Or.inr (hi _ h)
