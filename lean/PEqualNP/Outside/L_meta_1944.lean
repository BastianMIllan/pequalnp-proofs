import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1944
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

theorem ofFn_le {n : ℕ} (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true) :
    Le (List.ofFn x) (List.ofFn y) := by
  intro i hi
  rw [List.getD_eq_getElem?_getD] at hi ⊢
  by_cases hin : i < n
  · simp [List.getElem?_ofFn, hin] at hi ⊢
    exact h _ hi
  · simp [List.getElem?_ofFn, hin] at hi

theorem cf_mono (n : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true)
    (hx : PEqualNP.MetaComplexity.circuitFun n C x = true) :
    PEqualNP.MetaComplexity.circuitFun n C y = true := by
  unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval at *
  exact W_mono C.gates (fun g hg => (hC g hg).1) _ _ (by simp) (ofFn_le x y h) C.output hx

theorem append_le {n : ℕ} (a a' b b' : Fin n → Bool) (ha : ∀ i, a i = true → a' i = true)
    (hb : ∀ i, b i = true → b' i = true) :
    ∀ i, Fin.append a b i = true → Fin.append a' b' i = true := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]; exact ha j
  · simp only [Fin.append_right]; exact hb j

end PEqualNP.Outside.L_meta_1944

open PEqualNP.Outside.L_meta_1944 in
theorem PEqualNP.Outside.L_meta_1944 : (∀ (Nlv15 mlv15 : ℕ) (Clv15 : PEqualNP.CircuitLowerBounds.Circuit) (Slv15 Wlv15 : Finset (Fin Nlv15)) (pilv15 nulv15 : Fin Nlv15 → Bool) (sglv15 : ℕ → Fin 2), ((∀ glv15 ∈ Clv15.gates, (glv15.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15 + Nlv15) Clv15) → Set.ncard {jlv15 : ℕ | jlv15 < Clv15.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.Ico Nlv15 (Nlv15 + Nlv15))).getD ilv15 0 = 0) ∨ (∀ hlv15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.range Nlv15)).getD hlv15 0 = 0))} ≤ mlv15 + 1 → PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv15x1 : Fin Clv15.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.Ico Nlv15 (Nlv15 + Nlv15))).getD ilv15x1 0 = 0) ∨ (∀ hlv15x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.range Nlv15)).getD hlv15x1 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs.getD (sglv15 jlv15x1.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs.getD (sglv15 jlv15x1.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val))) Clv15.output) (Fin.append (fun plv15 : Fin Nlv15 => if plv15 ∈ Slv15 then (fun ulv15 : Fin Nlv15 => false) plv15 else pilv15 plv15) (fun llv15 : Fin Nlv15 => if llv15 ∈ Wlv15 then (fun ulv15x1 : Fin Nlv15 => false) llv15 else nulv15 llv15)) = true → PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Clv15 (Fin.append (fun plv15x1 : Fin Nlv15 => if plv15x1 ∈ Slv15 then (fun ulv15x2 : Fin Nlv15 => false) plv15x1 else pilv15 plv15x1) (fun llv15x1 : Fin Nlv15 => if llv15x1 ∈ Wlv15 then (fun ulv15x3 : Fin Nlv15 => false) llv15x1 else nulv15 llv15x1)) = false → (∃ xlv15 ylv15 : Fin Nlv15 → Bool, PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Clv15 (Fin.append (fun plv15x2 : Fin Nlv15 => if plv15x2 ∈ Slv15 then xlv15 plv15x2 else pilv15 plv15x2) (fun llv15x2 : Fin Nlv15 => if llv15x2 ∈ Wlv15 then ylv15 llv15x2 else nulv15 llv15x2)) = true) → ∃ Dlv15 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ glv15x1 ∈ Dlv15.gates, (glv15x1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15x1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15x1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15 + Nlv15) Dlv15) ∧ Set.ncard {jlv15x2 : ℕ | jlv15x2 < Dlv15.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x2).inputs, (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.Ico Nlv15 (Nlv15 + Nlv15))).getD ilv15x2 0 = 0) ∨ (∀ hlv15x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x2).inputs, (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.range Nlv15)).getD hlv15x2 0 = 0))} ≤ mlv15 ∧ Dlv15.size ≤ Clv15.size ∧ (0 < Dlv15.gates.length ∧ (∀ jlv15x3 < Dlv15.gates.length, ∀ ilv15x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x3).inputs, (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.image (fun plv15x3 : Fin Nlv15 => (plv15x3 : ℕ)) (Slv15)ᶜ ∪ Finset.image (fun llv15x3 : Fin Nlv15 => Nlv15 + (llv15x3 : ℕ)) (Wlv15)ᶜ)).getD ilv15x3 0 = 0) ∧ (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.image (fun plv15x4 : Fin Nlv15 => (plv15x4 : ℕ)) (Slv15)ᶜ ∪ Finset.image (fun llv15x4 : Fin Nlv15 => Nlv15 + (llv15x4 : ℕ)) (Wlv15)ᶜ)).getD Dlv15.output 0 = 0) ∧ ∀ xlv15x1 ylv15x1 : Fin Nlv15 → Bool, PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Dlv15 (Fin.append xlv15x1 ylv15x1) = PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Clv15 (Fin.append (fun plv15x5 : Fin Nlv15 => if plv15x5 ∈ Slv15 then xlv15x1 plv15x5 else pilv15 plv15x5) (fun llv15x5 : Fin Nlv15 => if llv15x5 ∈ Wlv15 then ylv15x1 llv15x5 else nulv15 llv15x5))) → ∀ (Nlv15b Klv15b mlv15b : ℕ) (Ilv15b : Fin Nlv15b → Fin Nlv15b → Prop) [DecidableRel Ilv15b] (Clv15b : PEqualNP.CircuitLowerBounds.Circuit) (Slv15b Wlv15b Xlv15b : Finset (Fin Nlv15b)) (wlv15b : Fin Nlv15b) (sglv15b : ℕ → Fin 2) (Splv15b Wplv15b : Finset (Fin Nlv15b)), ((∀ glv15b ∈ Clv15b.gates, (glv15b.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15b.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15b.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15b + Nlv15b) Clv15b) → Set.ncard {jlv15b : ℕ | jlv15b < Clv15b.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15b).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15b).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.Ico Nlv15b (Nlv15b + Nlv15b))).getD ilv15b 0 = 0) ∨ (∀ hlv15b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15b).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.range Nlv15b)).getD hlv15b 0 = 0))} ≤ mlv15b + 1 → ((0 < Clv15b.gates.length ∧ (∀ jlv15bx1 < Clv15b.gates.length, ∀ ilv15bx1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx1).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx5 : Fin Nlv15b => (plv15bx5 : ℕ)) (Slv15b)ᶜ ∪ Finset.image (fun llv15bx4 : Fin Nlv15b => Nlv15b + (llv15bx4 : ℕ)) (Wlv15b)ᶜ)).getD ilv15bx1 0 = 0) ∧ (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx6 : Fin Nlv15b => (plv15bx6 : ℕ)) (Slv15b)ᶜ ∪ Finset.image (fun llv15bx5 : Fin Nlv15b => Nlv15b + (llv15bx5 : ℕ)) (Wlv15b)ᶜ)).getD Clv15b.output 0 = 0) ∧ (∀ plv15bx3 ∈ Slv15b, ∀ llv15bx2 ∈ Wlv15b, Ilv15b plv15bx3 llv15bx2 → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Clv15b (Fin.append (fun plv15bx7 : Fin Nlv15b => decide (plv15bx7 ∈ ({plv15bx3} : Finset (Fin Nlv15b)))) (fun llv15bx6 : Fin Nlv15b => decide (llv15bx6 ∈ ({llv15bx2} : Finset (Fin Nlv15b))))) = true) ∧ (∀ Xlv15bx1 Ylv15b : Finset (Fin Nlv15b), Xlv15bx1 ⊆ Slv15b → Ylv15b ⊆ Wlv15b → Ylv15b.card ≤ Klv15b + 1 → (∀ plv15bx4 ∈ Xlv15bx1, ∀ llv15bx3 ∈ Ylv15b, ¬ Ilv15b plv15bx4 llv15bx3) → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Clv15b (Fin.append (fun plv15bx8 : Fin Nlv15b => decide (plv15bx8 ∈ Xlv15bx1)) (fun llv15bx7 : Fin Nlv15b => decide (llv15bx7 ∈ Ylv15b))) = false)) → wlv15b ∈ Wlv15b → Xlv15b ⊆ Slv15b → (∀ plv15bx1 ∈ Xlv15b, ¬ Ilv15b plv15bx1 wlv15b) → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv15bx2 : Fin Clv15b.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.Ico Nlv15b (Nlv15b + Nlv15b))).getD ilv15bx2 0 = 0) ∨ (∀ hlv15bx1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.range Nlv15b)).getD hlv15bx1 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs.getD (sglv15b jlv15bx2.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs.getD (sglv15b jlv15bx2.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val))) Clv15b.output) (Fin.append (fun plv15bx9 : Fin Nlv15b => decide (plv15bx9 ∈ Xlv15b)) (fun llv15bx8 : Fin Nlv15b => decide (llv15bx8 ∈ ({wlv15b} : Finset (Fin Nlv15b))))) = true → Splv15b = Slv15b.filter (fun ulv15b : Fin Nlv15b => ¬ Ilv15b ulv15b wlv15b ∧ ulv15b ∉ Xlv15b) → Wplv15b = Wlv15b.filter (fun llv15bx1 : Fin Nlv15b => llv15bx1 ≠ wlv15b ∧ ∀ plv15bx2 ∈ Xlv15b, ¬ Ilv15b plv15bx2 llv15bx1) → (∃ plv15b ∈ Splv15b, ∃ llv15b ∈ Wplv15b, Ilv15b plv15b llv15b) → ∃ Dlv15b : PEqualNP.CircuitLowerBounds.Circuit, ((∀ glv15bx1 ∈ Dlv15b.gates, (glv15bx1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15bx1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15bx1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15b + Nlv15b) Dlv15b) ∧ Set.ncard {jlv15bx3 : ℕ | jlv15bx3 < Dlv15b.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15bx3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx3).inputs, (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.Ico Nlv15b (Nlv15b + Nlv15b))).getD ilv15bx3 0 = 0) ∨ (∀ hlv15bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx3).inputs, (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.range Nlv15b)).getD hlv15bx2 0 = 0))} ≤ mlv15b ∧ Dlv15b.size ≤ Clv15b.size ∧ ((0 < Dlv15b.gates.length ∧ (∀ jlv15bx4 < Dlv15b.gates.length, ∀ ilv15bx4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx4).inputs, (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx12 : Fin Nlv15b => (plv15bx12 : ℕ)) (Splv15b)ᶜ ∪ Finset.image (fun llv15bx11 : Fin Nlv15b => Nlv15b + (llv15bx11 : ℕ)) (Wplv15b)ᶜ)).getD ilv15bx4 0 = 0) ∧ (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx13 : Fin Nlv15b => (plv15bx13 : ℕ)) (Splv15b)ᶜ ∪ Finset.image (fun llv15bx12 : Fin Nlv15b => Nlv15b + (llv15bx12 : ℕ)) (Wplv15b)ᶜ)).getD Dlv15b.output 0 = 0) ∧ (∀ plv15bx10 ∈ Splv15b, ∀ llv15bx9 ∈ Wplv15b, Ilv15b plv15bx10 llv15bx9 → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Dlv15b (Fin.append (fun plv15bx14 : Fin Nlv15b => decide (plv15bx14 ∈ ({plv15bx10} : Finset (Fin Nlv15b)))) (fun llv15bx13 : Fin Nlv15b => decide (llv15bx13 ∈ ({llv15bx9} : Finset (Fin Nlv15b))))) = true) ∧ (∀ Xlv15bx2 Ylv15bx1 : Finset (Fin Nlv15b), Xlv15bx2 ⊆ Splv15b → Ylv15bx1 ⊆ Wplv15b → Ylv15bx1.card ≤ Klv15b → (∀ plv15bx11 ∈ Xlv15bx2, ∀ llv15bx10 ∈ Ylv15bx1, ¬ Ilv15b plv15bx11 llv15bx10) → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Dlv15b (Fin.append (fun plv15bx15 : Fin Nlv15b => decide (plv15bx15 ∈ Xlv15bx2)) (fun llv15bx14 : Fin Nlv15b => decide (llv15bx14 ∈ Ylv15bx1))) = false)) := by
  intro H Nb Kb mb Ib _ Cb Sb Wb Xb wb sgb Spb Wpb hgood hcross hC hw hXS hXw hview hSp hWp hex
  obtain ⟨hreads, hacc, hrej⟩ := hC
  obtain ⟨p0, hp0, l0, hl0, hI0⟩ := hex
  have hSpS : ∀ p, p ∈ Spb → p ∈ Sb ∧ ¬ Ib p wb ∧ p ∉ Xb := by
    intro p hp; rw [hSp, Finset.mem_filter] at hp; exact ⟨hp.1, hp.2.1, hp.2.2⟩
  have hWpW : ∀ l, l ∈ Wpb → l ∈ Wb ∧ l ≠ wb ∧ ∀ p ∈ Xb, ¬ Ib p l := by
    intro l hl; rw [hWp, Finset.mem_filter] at hl; exact ⟨hl.1, hl.2.1, hl.2.2⟩
  have key := H Nb mb Cb Spb Wpb (fun p => decide (p ∈ Xb))
    (fun l => decide (l ∈ ({wb} : Finset (Fin Nb)))) sgb hgood hcross
  obtain ⟨D, hDgood, hDcross, hDsize, hDreads, hDfun⟩ := key
    (by
      convert hview using 3
      · funext p
        by_cases hp : p ∈ Spb
        · simp [hp, (hSpS p hp).2.2]
        · simp [hp]
      · funext l
        by_cases hl : l ∈ Wpb
        · simp [hl, (hWpW l hl).2.1]
        · simp [hl])
    (by
      by_contra hne
      rw [Bool.not_eq_false] at hne
      have h2 := cf_mono _ Cb hgood.1 _ (Fin.append (fun p => decide (p ∈ Xb))
        (fun l => decide (l ∈ ({wb} : Finset (Fin Nb))))) (by
          refine append_le _ _ _ _ ?_ ?_
          · intro q hq; by_cases hqs : q ∈ Spb <;> simp [hqs] at hq <;> simp [hq]
          · intro q hq; by_cases hqs : q ∈ Wpb <;> simp [hqs] at hq <;> simp [hq]) hne
      rw [hrej Xb {wb} hXS (by simpa using hw) (by simp)
        (by intro p hp l hl; rw [Finset.mem_singleton] at hl; subst hl; exact hXw p hp)] at h2
      exact Bool.false_ne_true h2)
    (by
      refine ⟨fun p => decide (p = p0), fun l => decide (l = l0), ?_⟩
      refine cf_mono _ Cb hgood.1 _ _ ?_ (hacc p0 (hSpS p0 hp0).1 l0 (hWpW l0 hl0).1 hI0)
      refine append_le _ _ _ _ ?_ ?_
      · intro q hq; simp at hq; subst hq; simp [hp0]
      · intro q hq; simp at hq; subst hq; simp [hl0])
  refine ⟨D, hDgood, hDcross, hDsize, hDreads, ?_, ?_⟩
  · intro p hp l hl hI
    rw [hDfun]
    refine cf_mono _ Cb hgood.1 _ _ ?_ (hacc p (hSpS p hp).1 l (hWpW l hl).1 hI)
    refine append_le _ _ _ _ ?_ ?_
    · intro q hq; simp at hq; subst hq; simp [hp]
    · intro q hq; simp at hq; subst hq; simp [hl]
  · intro X2 Y hX2 hY hYc hXY
    rw [hDfun]
    by_contra hne
    rw [Bool.not_eq_false] at hne
    have h2 := cf_mono _ Cb hgood.1 _ (Fin.append (fun p => decide (p ∈ Xb ∪ X2))
      (fun l => decide (l ∈ insert wb Y))) (by
        refine append_le _ _ _ _ ?_ ?_
        · intro q hq; by_cases hqs : q ∈ Spb <;> simp [hqs] at hq <;> simp [hq]
        · intro q hq; by_cases hqs : q ∈ Wpb <;> simp [hqs] at hq <;> simp [hq]) hne
    have hsub1 : Xb ∪ X2 ⊆ Sb := Finset.union_subset hXS (fun p hp => (hSpS p (hX2 hp)).1)
    have hsub2 : insert wb Y ⊆ Wb := Finset.insert_subset hw (fun l hl => (hWpW l (hY hl)).1)
    have hcard : (insert wb Y).card ≤ Kb + 1 := (Finset.card_insert_le _ _).trans (by omega)
    have hnoinc : ∀ p ∈ Xb ∪ X2, ∀ l ∈ insert wb Y, ¬ Ib p l := by
      intro p hp l hl
      rw [Finset.mem_union] at hp
      rw [Finset.mem_insert] at hl
      rcases hp with hp | hp <;> rcases hl with hl | hl
      · subst hl; exact hXw p hp
      · exact (hWpW l (hY hl)).2.2 p hp
      · subst hl; exact (hSpS p (hX2 hp)).2.1
      · exact hXY p hp l hl
    rw [hrej (Xb ∪ X2) (insert wb Y) hsub1 hsub2 hcard hnoinc] at h2
    exact Bool.false_ne_true h2
