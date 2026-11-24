import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2878

open PEqualNP.CircuitLowerBounds

theorem foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp
    omega

theorem wires_len (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact foldl_len C.gates x

theorem wires_snoc (C : Circuit) (op : GateOp) (a b o : ℕ) (x : List Bool) :
    Circuit.wires ⟨C.gates ++ [⟨op, [a, b]⟩], o⟩ x
      = C.wires x ++ [op.eval [(C.wires x).getD a false, (C.wires x).getD b false]] := by
  simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil]

end PEqualNP.Outside.L_meta_2878

theorem PEqualNP.Outside.L_meta_2878 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : PEqualNP.CircuitLowerBounds.GateOp), x4 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4 = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ (x6 x7 : ℕ), ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ x2.size + (1 : ℕ) ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x4.eval [(x2.wires (List.ofFn x9)).getD x6 Bool.false, (x2.wires (List.ofFn x9)).getD x7 Bool.false] := by
  intro n C hC op hop a b
  refine ⟨⟨C.gates ++ [⟨op, [a, b]⟩], n + C.gates.length⟩, ?_, ?_, ?_⟩
  · intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact hC g hg
    · simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      rcases hop with h | h <;> simp [h]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x
    rw [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.Outside.L_meta_2878.wires_snoc]
    have hl := PEqualNP.Outside.L_meta_2878.wires_len C (List.ofFn x)
    rw [List.length_ofFn] at hl
    dsimp only
    rw [← hl]
    simp [List.getD_eq_getElem?_getD]
