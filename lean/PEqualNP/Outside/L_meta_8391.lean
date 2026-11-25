import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8391
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem fun_mono (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true) :
    PEqualNP.MetaComplexity.circuitFun n C x = true →
    PEqualNP.MetaComplexity.circuitFun n C y = true := by
  intro h
  have hleg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    refine ⟨?_, (hC g hg).2⟩
    rcases (hC g hg).1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  exact mono2 C.gates hleg _ _ (by simp) (ofFn_mono n x y hxy) C.output h

end PEqualNP.Outside.L_meta_8391

open PEqualNP.Outside.L_meta_8391 in
theorem PEqualNP.Outside.L_meta_8391 : ∀ (x1 : ℕ) (x2 : Fin x1 → Finset (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x5 x6 : Fin x1), x5 ∈ x2 x6 → (PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 fun (x8 : Fin (x1 + x1)) => Decidable.decide (x8 = Fin.castAdd x1 x5 ∨ x8 = Fin.natAdd x1 x6)) = Bool.true) → (∀ (x6 : Finset (Fin x1)), (PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 fun (x7 : Fin (x1 + x1)) => Fin.addCases (fun (x8 : Fin x1) => Decidable.decide (x8 ∈ x6)) (fun (x8 : Fin x1) => Decidable.decide (∀ x9 ∈ x6, x9 ∉ x2 x8)) x7) = Bool.false) → ∀ (x7 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), x8 ∈ x2 x9 ∧ x7 (Fin.castAdd x1 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true) := by
  intro n S C hC hacc hrej x
  by_cases h : ∃ (p : Fin n) (l : Fin n), p ∈ S l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true
  · rw [decide_eq_true h]
    obtain ⟨p, l, hpl, h1, h2⟩ := h
    refine fun_mono (n + n) C hC _ x ?_ (hacc p l hpl)
    intro v hv
    simp only [decide_eq_true_eq] at hv
    rcases hv with rfl | rfl
    · exact h1
    · exact h2
  · rw [decide_eq_false h]
    by_contra hne
    have ht : PEqualNP.MetaComplexity.circuitFun (n + n) C x = true := by
      simpa using hne
    let X : Finset (Fin n) := Finset.univ.filter (fun p => x (Fin.castAdd n p) = true)
    have := fun_mono (n + n) C hC x (fun v => Fin.addCases (fun (q : Fin n) => decide (q ∈ X))
      (fun (q : Fin n) => decide (∀ r ∈ X, r ∉ S q)) v) ?_ ht
    · rw [hrej X] at this
      exact absurd this (by simp)
    · intro v hv
      induction v using Fin.addCases with
      | left p =>
        simp only [Fin.addCases_left, decide_eq_true_eq]
        simpa [X] using hv
      | right l =>
        simp only [Fin.addCases_right, decide_eq_true_eq]
        intro q hq hql
        exact h ⟨q, l, hql, by simpa [X] using hq, hv⟩
