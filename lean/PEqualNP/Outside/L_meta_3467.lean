import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3467

open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem eval_input (C : Circuit) (x : List Bool) (h : C.output < x.length) :
    C.eval x = x.getD C.output false := wf_keep C.gates x C.output h

theorem inc_len {N : ℕ} (X Y : Finset (Fin N)) :
    (PEqualNP.GenericRejection.incidenceInput X Y).length = N + N := by
  simp [PEqualNP.GenericRejection.incidenceInput]

theorem inc_pt {N : ℕ} (X Y : Finset (Fin N)) (o : ℕ) (ho : o < N) :
    (PEqualNP.GenericRejection.incidenceInput X Y).getD o false = decide ((⟨o, ho⟩ : Fin N) ∈ X) := by
  unfold PEqualNP.GenericRejection.incidenceInput
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; exact ho)]
  simp [ho]

theorem inc_ln {N : ℕ} (X Y : Finset (Fin N)) (o : ℕ) (h1 : N ≤ o) (h2 : o < N + N) :
    (PEqualNP.GenericRejection.incidenceInput X Y).getD o false =
      decide ((⟨o - N, by omega⟩ : Fin N) ∈ Y) := by
  unfold PEqualNP.GenericRejection.incidenceInput
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; exact h1)]
  simp [show o - N < N by omega]

end PEqualNP.Outside.L_meta_3467

theorem PEqualNP.Outside.L_meta_3467 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q N S C hq hN _ _ _ hout _ hsound
  exfalso
  by_cases ho : C.output < N
  · have h := hsound {⟨C.output, ho⟩} ∅ (by simp) (by intro l hl; simp at hl)
    rw [PEqualNP.Outside.L_meta_3467.eval_input C _
      (by rw [PEqualNP.Outside.L_meta_3467.inc_len]; omega),
      PEqualNP.Outside.L_meta_3467.inc_pt _ _ _ ho] at h
    simp at h
  · have h1 : N ≤ C.output := by omega
    have h := hsound ∅ {⟨C.output - N, by omega⟩} (by simp; omega)
      (by intro l _; exact Finset.disjoint_empty_right _)
    rw [PEqualNP.Outside.L_meta_3467.eval_input C _
      (by rw [PEqualNP.Outside.L_meta_3467.inc_len]; omega),
      PEqualNP.Outside.L_meta_3467.inc_ln _ _ _ h1 hout] at h
    simp at h
