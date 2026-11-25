import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10252

open PEqualNP.CircuitLowerBounds

-- Each half of three inputs gives its thresholds T1, T2, T3, then exactly-one and
-- exactly-two; the count is divisible by three when both halves have residue zero, or
-- residues one and two in either order. In all 28 gates.
def gA (i j : ℕ) : Gate := ⟨GateOp.and, [i, j]⟩
def gO (i j : ℕ) : Gate := ⟨GateOp.or, [i, j]⟩
def gN (i : ℕ) : Gate := ⟨GateOp.not, [i]⟩

def gs : List Gate :=
  [gA 0 1, gO 0 1, gA 2 7, gO 8 6, gO 7 2, gA 6 2, gN 9, gN 11, gA 10 12, gA 9 13,
   gA 3 4, gO 3 4, gA 5 17, gO 18 16, gO 17 5, gA 16 5, gN 19, gN 21, gA 20 22, gA 19 23,
   gO 14 15, gO 24 25, gO 26 27, gN 28, gA 14 25, gA 15 24, gO 30 31, gO 29 32]

def circ : Circuit := ⟨gs, 33⟩

theorem fan : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp only [circ, gs, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    simp [gA, gO, gN]

theorem tab : ∀ a b c d e f : Bool,
    circ.eval [a, b, c, d, e, f] = decide (([a, b, c, d, e, f] : List Bool).count true % 3 = 0) := by
  decide

end PEqualNP.Outside.L_meta_10252

theorem PEqualNP.Outside.L_meta_10252 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => decide (((List.ofFn x).count true) % 3 = 0)) 36 := by
  refine ⟨PEqualNP.Outside.L_meta_10252.circ, PEqualNP.Outside.L_meta_10252.fan, by decide, ?_⟩
  intro x
  have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    simp [List.ofFn_succ]
  rw [h]
  exact PEqualNP.Outside.L_meta_10252.tab _ _ _ _ _ _
