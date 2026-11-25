import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7340

open PEqualNP.CircuitLowerBounds

def clampGate (N : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map fun i => min i N⟩

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_clamp (w : List Bool) (N i : ℕ) (hw : w.length ≤ N) :
    w.getD (min i N) false = w.getD i false := by
  by_cases h : i ≤ N
  · rw [Nat.min_eq_left h]
  · push_neg at h
    rw [Nat.min_eq_right h.le]
    rw [List.getD_eq_default _ _ hw, List.getD_eq_default _ _ (by omega)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_clamp (N : ℕ) (gs : List Gate) (w : List Bool)
    (h : w.length + gs.length ≤ N) :
    (gs.map (clampGate N)).foldl stepW w = gs.foldl stepW w := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hs : stepW w (clampGate N g) = stepW w g := by
      simp only [stepW, clampGate, List.map_map]
      congr 3
      apply List.map_congr_left
      intro i _
      simp only [Function.comp]
      exact getD_clamp w N i (by simp at h; omega)
    rw [hs]
    apply ih
    simp [stepW]
    simp at h
    omega

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

end PEqualNP.Outside.L_meta_7340

theorem PEqualNP.Outside.L_meta_7340 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x6 ∧ x6.size ≤ x2 ∧ x6.output ≤ x1 + x2 ∧ (∀ x7 ∈ x6.gates, ∀ x9 ∈ x7.inputs, x9 ≤ x1 + x2) ∧ ∀ (x7 : List Bool), x7.length = x1 → x6.eval x7 = x3.eval x7 := by
  intro x1 x2 C hC hs
  refine ⟨⟨C.gates.map (PEqualNP.Outside.L_meta_7340.clampGate (x1 + x2)),
    min C.output (x1 + x2)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨h1, h2⟩ := hC g0 hg0
    refine ⟨h1, ?_⟩
    simpa [PEqualNP.Outside.L_meta_7340.clampGate] using h2
  · simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hs
  · exact Nat.min_le_right _ _
  · intro g hg i hi
    simp only [List.mem_map] at hg
    obtain ⟨g0, _, rfl⟩ := hg
    simp only [PEqualNP.Outside.L_meta_7340.clampGate, List.mem_map] at hi
    obtain ⟨j, _, rfl⟩ := hi
    exact Nat.min_le_right _ _
  · intro x hx
    have hs' : C.gates.length ≤ x2 := hs
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.Outside.L_meta_7340.wires_eq]
    rw [PEqualNP.Outside.L_meta_7340.foldl_clamp (x1 + x2) C.gates x (by omega)]
    apply PEqualNP.Outside.L_meta_7340.getD_clamp
    rw [PEqualNP.Outside.L_meta_7340.foldl_len]
    omega
