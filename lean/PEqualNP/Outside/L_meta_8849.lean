import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8849

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

def Le (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, w.getD i false = true → w'.getD i false = true

theorem le_append {a a' b b' : List Bool} (h : Le a a') (h2 : Le b b') :
    Le (a ++ b) (a' ++ b') := by
  obtain ⟨hl, hp⟩ := h
  obtain ⟨hl2, hp2⟩ := h2
  refine ⟨by simp [hl, hl2], fun i hi => ?_⟩
  have hp' := hp i
  have hp2' := hp2 (i - a.length)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append] at hi hp' hp2' ⊢
  rw [← hl]
  by_cases hlt : i < a.length
  · simp only [hlt, ite_true] at hi ⊢
    exact hp' hi
  · simp only [hlt, ite_false] at hi ⊢
    exact hp2' hi

theorem le_snoc {w w' : List Bool} {v v' : Bool} (h : Le w w') (hv : v = true → v' = true) :
    Le (w ++ [v]) (w' ++ [v']) := by
  refine le_append h ⟨rfl, fun i hi => ?_⟩
  cases i with
  | zero => simpa using hv (by simpa using hi)
  | succ k => simp at hi

theorem gate_mono {w w' : List Bool} (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (h : Le w w') :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun H i hi => h.2 i (H i hi)
  · rw [hg]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, H⟩ => ⟨i, hi, h.2 i H⟩

theorem fold_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w w' : List Bool), Le w w' →
      Le (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
         (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    intro w w' h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (le_snoc h (gate_mono g (hgs g List.mem_cons_self) h))

theorem ofFn_le {n : ℕ} (a b : Fin n → Bool) (h : ∀ k, a k = true → b k = true) :
    Le (List.ofFn a) (List.ofFn b) := by
  refine ⟨by simp, fun i hi => ?_⟩
  simp only [List.getD_eq_getElem?_getD] at hi ⊢
  by_cases hlt : i < n
  · simp only [List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some] at hi ⊢
    exact h _ hi
  · simp [hlt] at hi

theorem eval_mono {n m : ℕ} (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    {X X' : Finset (Fin n)} {Y Y' : Finset (Fin m)} (hX : X ⊆ X') (hY : Y ⊆ Y') :
    C.eval (incidenceInput X Y) = true → C.eval (incidenceInput X' Y') = true := by
  unfold Circuit.eval Circuit.wires incidenceInput
  refine (fold_mono C.gates hC _ _ (le_append (ofFn_le _ _ ?_) (ofFn_le _ _ ?_))).2 C.output
  · intro k hk
    simpa using hX (by simpa using hk)
  · intro k hk
    simpa using hY (by simpa using hk)

end PEqualNP.Outside.L_meta_8849

theorem PEqualNP.Outside.L_meta_8849 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x1) x2 → ∀ (x4 x5 x6 x7 : Finset (Fin x1)), x4 ⊆ x6 → x5 ⊆ x7 → x2.eval (PEqualNP.GenericRejection.incidenceInput x4 x5) = Bool.true → x2.eval (PEqualNP.GenericRejection.incidenceInput x6 x7) = Bool.true := by
  intro x1 x2 hA x4 x5 x6 x7 h46 h57 h
  exact PEqualNP.Outside.L_meta_8849.eval_mono x2 hA.1 h46 h57 h
