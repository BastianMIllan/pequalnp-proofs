import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7163

open PEqualNP.CircuitLowerBounds

theorem foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [Nat.add_comm, Nat.add_left_comm]

theorem wires_len (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact foldl_len _ _

theorem wires_snoc (C : Circuit) (g : Gate) (x : List Bool) :
    (Circuit.mk (C.gates ++ [g]) C.output).wires x
      = C.wires x ++ [g.op.eval (g.inputs.map fun i => (C.wires x).getD i false)] := by
  unfold Circuit.wires
  rw [List.foldl_append]
  rfl

end PEqualNP.Outside.L_meta_7163

theorem PEqualNP.Outside.L_meta_7163 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : Bool) (x5 x6 : ℕ), ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x7.size ≤ x2.size + (1 : ℕ) ∧ ∀ (x8 : Fin x1 → Bool), x7.eval (List.ofFn x8) = (if x4 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or).eval [(x2.wires (List.ofFn x8)).getD x5 Bool.false, (x2.wires (List.ofFn x8)).getD x6 Bool.false] := by
  intro x1 x2 hM x4 x5 x6
  let g : PEqualNP.CircuitLowerBounds.Gate :=
    ⟨if x4 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and
      else PEqualNP.CircuitLowerBounds.GateOp.or, [x5, x6]⟩
  refine ⟨⟨x2.gates ++ [g], x1 + x2.gates.length⟩, ?_, ?_, ?_⟩
  · intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact hM h hh
    · rw [List.mem_singleton] at hh
      subst hh
      refine ⟨?_, by simp [g]⟩
      by_cases h4 : x4 = Bool.true
      · simp [g, h4]
      · simp [g, h4]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x8
    have hw := PEqualNP.Outside.L_meta_7163.wires_snoc
      ⟨x2.gates, x1 + x2.gates.length⟩ g (List.ofFn x8)
    have hl := PEqualNP.Outside.L_meta_7163.wires_len x2 (List.ofFn x8)
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    simp only at hw ⊢
    have hx2 : (⟨x2.gates, x1 + x2.gates.length⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires
        (List.ofFn x8) = x2.wires (List.ofFn x8) := rfl
    rw [hw, hx2]
    have hlen : (x2.wires (List.ofFn x8)).length = x1 + x2.gates.length := by
      rw [hl, List.length_ofFn]
    rw [List.getD_eq_getElem _ _ (by simp [hlen])]
    simp [hlen, g]
