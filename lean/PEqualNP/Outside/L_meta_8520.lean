import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8520

open PEqualNP.CircuitLowerBounds

def pre (x3 : Bool) (x4 x5 : ℕ) : Gate :=
  if x4 = 56 then (if x3 = true then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩)
  else (if x3 = true then ⟨GateOp.and, [x4, x5]⟩ else ⟨GateOp.or, [x4, x5]⟩)

theorem pre_mono (x3 : Bool) (x4 x5 : ℕ) :
    (pre x3 x4 x5).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (pre x3 x4 x5).inputs.length ≤ 2 := by
  unfold pre
  split_ifs <;> simp

theorem pre_eval (x3 : Bool) (x4 x5 : ℕ) (x7 : List Bool) :
    (pre x3 x4 x5).op.eval ((pre x3 x4 x5).inputs.map fun i => x7.getD i false) =
      (if x4 = (56 : ℕ) then x3 else if x3 = Bool.true then x7.getD x4 Bool.false && x7.getD x5 Bool.false
        else x7.getD x4 Bool.false || x7.getD x5 Bool.false) := by
  unfold pre
  cases x3 <;> by_cases h : x4 = 56 <;> simp [h, GateOp.eval]

end PEqualNP.Outside.L_meta_8520

theorem PEqualNP.Outside.L_meta_8520 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∀ (x3 : Bool) (x4 x5 : ℕ), ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x1.size + (1 : ℕ) ∧ ∀ (x7 : List Bool), x6.eval x7 = x1.eval (x7 ++ [if x4 = (56 : ℕ) then x3 else if x3 = Bool.true then x7.getD x4 Bool.false && x7.getD x5 Bool.false else x7.getD x4 Bool.false || x7.getD x5 Bool.false]) := by
  intro x1 hx1 x3 x4 x5
  refine ⟨⟨PEqualNP.Outside.L_meta_8520.pre x3 x4 x5 :: x1.gates, x1.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | h
    · exact PEqualNP.Outside.L_meta_8520.pre_mono x3 x4 x5
    · exact hx1 g h
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x7
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl_cons]
    rw [PEqualNP.Outside.L_meta_8520.pre_eval]
