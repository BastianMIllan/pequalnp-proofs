import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2880

open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : t - l.length ≠ 0 := by omega
      simp [List.getElem?_cons, this]

def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

theorem gate_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩

theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) : Le (W gs x) (W gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (W gs x).length = (W gs y).length := by simp [W_length, hl]
    rw [W_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (W gs x).length
    · rw [if_pos h1] at ht ⊢; exact ih t ht
    · rw [if_neg h1] at ht ⊢
      by_cases h2 : t = (W gs x).length
      · rw [if_pos h2] at ht ⊢
        exact gate_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [if_neg h2] at ht; simp at ht

theorem ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hn : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hn⟩ := by
  simp [List.getD_eq_getElem?_getD, hn]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hn : ¬ i < n) :
    (List.ofFn x).getD i false = false := by
  simp [List.getD_eq_getElem?_getD, hn]

theorem ofFn_le {n : ℕ} (x y : Fin n → Bool) (h : x ≤ y) : Le (List.ofFn x) (List.ofFn y) := by
  intro i hi
  by_cases hn : i < n
  · rw [ofFn_getD_lt x i hn] at hi
    rw [ofFn_getD_lt y i hn]
    have := h ⟨i, hn⟩
    rw [hi] at this
    revert this
    cases y ⟨i, hn⟩ <;> simp
  · rw [ofFn_getD_ge x i hn] at hi
    exact absurd hi Bool.false_ne_true

theorem eval_mono {n : ℕ} (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (h : x ≤ y) (hx : C.eval (List.ofFn x) = true) :
    C.eval (List.ofFn y) = true := by
  have hm : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  have := W_mono C.gates hm (List.ofFn x) (List.ofFn y) (by simp) (ofFn_le x y h) C.output
  exact this hx

end PEqualNP.Outside.L_meta_2880

theorem PEqualNP.Outside.L_meta_2880 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : (Fin x1 → Bool) → Prop), (∀ (x5 : Fin x1 → Bool), Minimal x4 x5 → x2.eval (List.ofFn x5) = Bool.true) → (∀ (x6 : Fin x1 → Bool), Maximal (fun (x7 : Fin x1 → Bool) => ¬x4 x7) x6 → x2.eval (List.ofFn x6) = Bool.false) → ∀ (x7 : Fin x1 → Bool), x2.eval (List.ofFn x7) = Bool.true ↔ x4 x7 := by
  intro n C hC P hmin hmax x
  constructor
  · intro hx
    by_contra hP
    obtain ⟨z, hxz, hz⟩ := exists_maximal_ge_of_wellFoundedGT (fun y => ¬ P y) x hP
    have h1 := hmax z hz
    have h2 := PEqualNP.Outside.L_meta_2880.eval_mono C hC x z hxz hx
    rw [h1] at h2
    exact Bool.false_ne_true h2
  · intro hP
    obtain ⟨y, hyx, hy⟩ := exists_minimal_le_of_wellFoundedLT P x hP
    exact PEqualNP.Outside.L_meta_2880.eval_mono C hC y x hyx (hmin y hy)
