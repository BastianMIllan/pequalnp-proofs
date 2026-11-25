import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7093
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem getD_snoc_eq (L : List Bool) (a : Bool) (k : ℕ) (hk : k = L.length) :
    (L ++ [a]).getD k false = a := by
  subst hk
  simp [List.getD_eq_getElem?_getD]

theorem gateAt_snoc (gs : List Gate) (o : ℕ) (g : Gate) (j : ℕ) (hj : j < gs.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs ++ [g], o⟩ j
      = PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, o⟩ j := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hj]

theorem gateAt_last (gs : List Gate) (o : ℕ) (g : Gate) :
    PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs ++ [g], o⟩ gs.length = g := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_7093

open PEqualNP.Outside.L_meta_7093 in
theorem PEqualNP.Outside.L_meta_7093 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3.inputs.length ≤ (2 : ℕ) → (∀ x8 ∈ x3.inputs, x8 < x1 + x2.size) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x9 ∧ x9.size = x2.size + (1 : ℕ) ∧ ∀ (x10 : List Bool), x10.length = x1 → x9.eval x10 = x3.op.eval (List.map (fun (x12 : ℕ) => (x2.wires x10).getD x12 Bool.false) x3.inputs) := by
  intro n C g hM hR hop hlen hin
  refine ⟨⟨C.gates ++ [g], n + C.gates.length⟩, ?_, ?_, ?_, ?_⟩
  · intro h hh
    rcases List.mem_append.1 hh with hh | hh
    · exact hM h hh
    · rw [List.mem_singleton] at hh
      subst hh
      refine ⟨?_, hlen⟩
      rcases hop with e | e <;> rw [e] <;> simp
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [gateAt_snoc C.gates _ g j hj] at hi
      exact hR j hj i hi
    · subst hj
      rw [gateAt_last] at hi
      exact hin i hi
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x hx
    have e1 : PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.gates ++ [g], n + C.gates.length⟩ x
        = wf (C.gates ++ [g]) x := rfl
    have e2 : C.wires x = wf C.gates x := rfl
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval]
    rw [e1, e2, wf_snoc]
    exact getD_snoc_eq _ _ _ (by rw [wf_len, hx])
