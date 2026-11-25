import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9071

open PEqualNP.CircuitLowerBounds

theorem keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = w.getD i false := by
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem evalIn (C : Circuit) (x : List Bool) (h : C.output < x.length) :
    C.eval x = x.getD C.output false := by
  unfold Circuit.eval Circuit.wires
  exact keep C.gates x C.output h

end PEqualNP.Outside.L_meta_9071

theorem PEqualNP.Outside.L_meta_9071 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (26 : ℕ) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x5 ≠ (0 : Fin (13 : ℕ)) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) → (59 : ℕ) ≤ x1.size := by
  intro C ho _ hC
  exfalso
  have h1 : C.eval (List.ofFn (fun j : Fin 26 => decide (j.val = C.output))) = true := by
    rw [PEqualNP.Outside.L_meta_9071.evalIn _ _ (by simpa using ho)]
    rw [List.getD_eq_getElem _ _ (by simpa using ho), List.getElem_ofFn]
    simp
  obtain ⟨a, b, _, _, ha, hb⟩ := (hC _).1 h1
  simp only [decide_eq_true_eq, Fin.coe_castAdd, Fin.coe_natAdd] at ha hb
  have := a.isLt
  omega
