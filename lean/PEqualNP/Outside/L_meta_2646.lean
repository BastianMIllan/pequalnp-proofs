import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2646
open PEqualNP PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

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

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
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
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [if_neg h2] at ht; simp at ht

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [dif_pos h, List.getElem?_ofFn]
    simp [h]
  · rw [dif_neg h, List.getElem?_eq_none (by simp; omega)]
    rfl

theorem fun_mono (n : ℕ) (C : Circuit) (hC : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) (hx : circuitFun n C x = true) :
    circuitFun n C y = true := by
  have hm : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h1 := (hC g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact h1
  have hle : Le (List.ofFn x) (List.ofFn y) := by
    intro i hi
    rw [ofFn_getD] at hi ⊢
    by_cases h : i < n
    · rw [dif_pos h] at hi ⊢; exact hxy _ hi
    · rw [dif_neg h] at hi; exact absurd hi (by simp)
  have hW := W_mono C.gates hm (List.ofFn x) (List.ofFn y) (by simp) hle
  have hx' : (W C.gates (List.ofFn x)).getD C.output false = true := hx
  exact hW _ hx'

end PEqualNP.Outside.L_meta_2646

theorem PEqualNP.Outside.L_meta_2646 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : ℕ) (x5 : Fin x1 → Bool), (∀ (x6 : Fin x1), x5 x6 = Bool.true → x4.testBit ↑x6 = Bool.true) → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x7 : Fin x1) => x4.testBit ↑x7) = Bool.false → PEqualNP.MetaComplexity.circuitFun x1 x2 x5 = Bool.false := by
  intro n C hC k x hxk hk
  cases h : PEqualNP.MetaComplexity.circuitFun n C x with
  | false => rfl
  | true =>
    have := PEqualNP.Outside.L_meta_2646.fun_mono n C hC x (fun i => k.testBit i) hxk h
    rw [hk] at this
    exact absurd this (by simp)
