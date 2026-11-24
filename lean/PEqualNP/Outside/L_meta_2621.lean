import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2621

open PEqualNP.CircuitLowerBounds

-- the gate value combining two operand wires
def comb (op : GateOp) (x4 : List Bool) (a b : ℕ) (va vb : Bool) : Bool :=
  match op with
  | GateOp.and => (x4.getD a false && vb || va && x4.getD b false)
  | _ => (va || vb)

-- the wire values, by strong recursion on the wire index
def wv (C : Circuit) (s : ℕ) (x4 : List Bool) (n : ℕ) : Bool :=
  if n < 26 then decide (n = s) else
  match C.gates[n - 26]? with
  | none => false
  | some g =>
    if ha : g.inputs.getD 0 0 < n then
      if hb : g.inputs.getD 1 0 < n then
        comb g.op x4 (g.inputs.getD 0 0) (g.inputs.getD 1 0)
          (wv C s x4 (g.inputs.getD 0 0)) (wv C s x4 (g.inputs.getD 1 0))
      else false
    else false
termination_by n

theorem wv_lt (C : Circuit) (s : ℕ) (x4 : List Bool) (n : ℕ) (h : n < 26) :
    wv C s x4 n = decide (n = s) := by
  rw [wv]; simp [h]

theorem wv_gate (C : Circuit) (s : ℕ) (x4 : List Bool) (j : ℕ) (g : Gate) (a b : ℕ)
    (hg : C.gates[j]? = some g) (hin : g.inputs = [a, b]) (ha : a < 26 + j) (hb : b < 26 + j) :
    wv C s x4 (26 + j) = comb g.op x4 a b (wv C s x4 a) (wv C s x4 b) := by
  rw [wv]
  have h1 : ¬ (26 + j < 26) := by omega
  have h2 : 26 + j - 26 = j := by omega
  simp only [h1, if_false, h2, hg, hin]
  simp [ha, hb]

end PEqualNP.Outside.L_meta_2621

theorem PEqualNP.Outside.L_meta_2621 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → ∀ (x3 : ℕ) (x4 : List Bool), ∃ (x5 : ℕ → Bool), (∀ x6 < (26 : ℕ), x5 x6 = Decidable.decide (x6 = x3)) ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ), x1.gates[x6]? = Option.some x7 → x7.inputs = [x8, x9] → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x6) = (x4.getD x8 Bool.false && x5 x9 || x5 x8 && x4.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9)) := by
  intro x1 hC x3 x4
  refine ⟨PEqualNP.Outside.L_meta_2621.wv x1 x3 x4, ?_, ?_⟩
  · intro x6 h6
    exact PEqualNP.Outside.L_meta_2621.wv_lt x1 x3 x4 x6 h6
  · intro x6 x7 x8 x9 hg hin
    have hlen : x6 < x1.gates.length := by
      rcases List.getElem?_eq_some_iff.mp hg with ⟨h, _⟩
      exact h
    have hat : PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6 = x7 := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem?_getD, hg]
      rfl
    have hrb := hC.2.1 x6 hlen
    rw [hat, hin] at hrb
    have ha : x8 < 26 + x6 := hrb x8 (by simp)
    have hb : x9 < 26 + x6 := hrb x9 (by simp)
    have key := PEqualNP.Outside.L_meta_2621.wv_gate x1 x3 x4 x6 x7 x8 x9 hg hin ha hb
    refine ⟨fun hop => ?_, fun hop => ?_⟩
    · rw [key, hop]; rfl
    · rw [key, hop]; rfl
