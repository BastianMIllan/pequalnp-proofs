import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6458

open PEqualNP.CircuitLowerBounds

theorem foldl_len (L : List Gate) (x : List Bool) :
    (L.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length
      = x.length + L.length := by
  induction L generalizing x with
  | nil => simp
  | cons g L ih =>
    rw [List.foldl_cons, ih]
    simp
    omega

theorem wires_len (L : List Gate) (o : ℕ) (x : List Bool) :
    (Circuit.wires ⟨L, o⟩ x).length = x.length + L.length := by
  unfold Circuit.wires
  exact foldl_len L x

theorem wires_snoc (L : List Gate) (h : Gate) (o : ℕ) (x : List Bool) :
    Circuit.wires ⟨L ++ [h], o⟩ x = Circuit.wires ⟨L, o⟩ x ++
      [h.op.eval (h.inputs.map fun i => (Circuit.wires ⟨L, o⟩ x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem gd_left (W : List Bool) (v : Bool) (n : ℕ) (h : n < W.length) :
    (W ++ [v]).getD n false = W.getD n false := List.getD_append _ _ _ _ h

theorem gd_right (W : List Bool) (v : Bool) (n : ℕ) (h : n = W.length) :
    (W ++ [v]).getD n false = v := by
  subst h
  simp

end PEqualNP.Outside.L_meta_6458

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_6458 in
theorem PEqualNP.Outside.L_meta_6458 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x2.size), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x6 : Fin x2.gates.length), ∀ x7 ∈ (x2.gates.get x6).inputs, x7 ≤ x1 + ↑x6) → x3 ≤ x4 → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), x8.size = x2.size ∧ PEqualNP.MetaComplexity.Monotone2 x8 ∧ (∀ (x9 : Fin x8.gates.length), ∀ x10 ∈ (x8.gates.get x9).inputs, x10 ≤ x1 + ↑x9) ∧ ∀ (x9 : List Bool), x9.length = x1 → ((x8.wires x9).getD (x1 + ↑x3) Bool.false && (x8.wires x9).getD (x1 + (x8.size - (1 : ℕ))) Bool.false) = ((x2.wires x9).getD (x1 + ↑x3) Bool.false && (x2.wires x9).getD (x1 + ↑x4) Bool.false) := by
  intro x1 x2 x3 x4 hmono hin h34
  obtain ⟨gates, out⟩ := x2
  have h34' : (x3 : ℕ) ≤ (x4 : ℕ) := h34
  by_cases hcase : (x4 : ℕ) + 1 = gates.length
  · refine ⟨⟨gates, out⟩, rfl, hmono, hin, ?_⟩
    intro x9 _
    have hs : Circuit.size ⟨gates, out⟩ - 1 = (x4 : ℕ) := by
      simp only [Circuit.size]
      omega
    rw [hs]
  · have hpos := x3.isLt
    simp only [Circuit.size] at hpos
    have hne : gates ≠ [] := List.ne_nil_of_length_pos (by omega)
    obtain ⟨L, g, rfl⟩ : ∃ L g, gates = L ++ [g] :=
      ⟨gates.dropLast, gates.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    have hx4' := x4.isLt
    simp only [Circuit.size, List.length_append, List.length_singleton] at hx4' hcase
    have hx4 : (x4 : ℕ) < L.length := by omega
    have hx3 : (x3 : ℕ) < L.length := by omega
    dsimp only at hmono hin
    refine ⟨⟨L ++ [(⟨GateOp.and, [x1 + (x4 : ℕ)]⟩ : Gate)], out⟩, by simp [Circuit.size], ?_, ?_, ?_⟩
    · intro g' hg'
      simp only [List.mem_append, List.mem_singleton] at hg'
      rcases hg' with hg' | rfl
      · exact hmono g' (by simp [hg'])
      · simp
    · intro x9 x10 hx10
      have hx9 := x9.isLt
      simp only [List.length_append, List.length_singleton] at hx9
      by_cases hlt : (x9 : ℕ) < L.length
      · have e1 : (L ++ [(⟨GateOp.and, [x1 + (x4 : ℕ)]⟩ : Gate)]).get x9 = L[(x9 : ℕ)] := by
          simp [List.get_eq_getElem, List.getElem_append_left hlt]
        have hlt2 : (x9 : ℕ) < (L ++ [g]).length := by simp; omega
        have e2 : (L ++ [g]).get ⟨x9, hlt2⟩ = L[(x9 : ℕ)] := by
          simp [List.get_eq_getElem, List.getElem_append_left hlt]
        rw [e1] at hx10
        have := hin ⟨x9, hlt2⟩ x10 (by rw [e2]; exact hx10)
        simpa using this
      · have hEq : (x9 : ℕ) = L.length := by omega
        have e1 : (L ++ [(⟨GateOp.and, [x1 + (x4 : ℕ)]⟩ : Gate)]).get x9
            = ⟨GateOp.and, [x1 + (x4 : ℕ)]⟩ := by
          simp [List.get_eq_getElem, hEq]
        rw [e1] at hx10
        simp at hx10
        omega
    · intro x9 hlen
      have hW : (Circuit.wires ⟨L, out⟩ x9).length = x1 + L.length := by
        rw [wires_len, hlen]
      have hs : Circuit.size ⟨L ++ [(⟨GateOp.and, [x1 + (x4 : ℕ)]⟩ : Gate)], out⟩ - 1 = L.length := by
        simp [Circuit.size]
      rw [hs, wires_snoc, wires_snoc]
      rw [gd_left _ _ (x1 + (x3 : ℕ)), gd_left _ _ (x1 + (x3 : ℕ)), gd_left _ _ (x1 + (x4 : ℕ)),
        gd_right _ _ (x1 + L.length)]
      · simp [GateOp.eval]
      all_goals omega
