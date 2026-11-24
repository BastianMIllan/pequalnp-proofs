import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3012
open PEqualNP.CircuitLowerBounds

def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

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

theorem ofFn_le {n : ℕ} (x y : Fin n → Bool) (hxy : x ≤ y) : Le (List.ofFn x) (List.ofFn y) := by
  intro i h
  by_cases hi : i < n
  · simp [List.getD_eq_getElem?_getD, hi] at h ⊢
    have := hxy ⟨i, hi⟩
    rw [h] at this
    exact le_antisymm (Bool.le_true _) this
  · simp [List.getD_eq_getElem?_getD, hi] at h

theorem circ_mono {n : ℕ} (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (x y : Fin n → Bool) (hxy : x ≤ y) (h : C.eval (List.ofFn x) = true) :
    C.eval (List.ofFn y) = true := by
  have hm : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := hC.1
  have := W_mono C.gates hm (List.ofFn x) (List.ofFn y) (by simp) (ofFn_le x y hxy) C.output
  exact this h

end PEqualNP.Outside.L_meta_3012

theorem PEqualNP.Outside.L_meta_3012 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : (Fin x1 → Bool) → Bool), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ (x5 : Fin x1 → Bool), x3 x5 = Bool.true → (∀ x7 ≤ x5, x3 x7 = Bool.true → x7 = x5) → x2.eval (List.ofFn x5) = Bool.true) → (∀ (x6 : Fin x1 → Bool), x3 x6 = Bool.false → (∀ (x8 : Fin x1 → Bool), x6 ≤ x8 → x3 x8 = Bool.false → x8 = x6) → x2.eval (List.ofFn x6) = Bool.false) → ∀ (x7 : Fin x1 → Bool), x2.eval (List.ofFn x7) = x3 x7 := by
  intro n C f hC hT hF x
  have hTrue : ∀ z : Fin n → Bool, f z = true → C.eval (List.ofFn z) = true := by
    intro z
    induction z using WellFoundedLT.induction with
    | _ z ih =>
      intro hz
      by_cases hmin : ∀ w ≤ z, f w = true → w = z
      · exact hT z hz hmin
      · push_neg at hmin
        obtain ⟨w, hwz, hw, hne⟩ := hmin
        exact PEqualNP.Outside.L_meta_3012.circ_mono C hC w z hwz (ih w (lt_of_le_of_ne hwz hne) hw)
  have hFalse : ∀ z : Fin n → Bool, f z = false → C.eval (List.ofFn z) = false := by
    intro z
    induction z using WellFoundedGT.induction with
    | _ z ih =>
      intro hz
      by_cases hmax : ∀ w : Fin n → Bool, z ≤ w → f w = false → w = z
      · exact hF z hz hmax
      · push_neg at hmax
        obtain ⟨w, hzw, hw, hne⟩ := hmax
        have hwv := ih w (lt_of_le_of_ne hzw (Ne.symm hne)) hw
        cases hz' : C.eval (List.ofFn z)
        · rfl
        · have := PEqualNP.Outside.L_meta_3012.circ_mono C hC z w hzw hz'
          rw [hwv] at this
          exact absurd this (by decide)
  cases hfx : f x
  · exact hFalse x hfx
  · exact hTrue x hfx
