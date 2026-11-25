import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8295

open PEqualNP.CircuitLowerBounds

theorem split_last {α : Type} (p : α → Prop) : ∀ (l : List α), (∃ x ∈ l, p x) →
    ∃ (A : List α) (g : α) (B : List α), l = A ++ g :: B ∧ p g ∧ ∀ b ∈ B, ¬ p b
  | [], h => by simp at h
  | a :: t, h => by
    by_cases ht : ∃ x ∈ t, p x
    · obtain ⟨A, g, B, hl, hg, hB⟩ := split_last p t ht
      exact ⟨a :: A, g, B, by rw [hl]; rfl, hg, hB⟩
    · refine ⟨[], a, t, rfl, ?_, ?_⟩
      · obtain ⟨x, hx, hpx⟩ := h
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hpx
        · exact absurd ⟨x, hx, hpx⟩ ht
      · intro b hb hpb
        exact ht ⟨b, hb, hpb⟩

theorem len_foldl (A : List Gate) : ∀ (w : List Bool),
    (A.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + A.length := by
  induction A with
  | nil => intro w; simp
  | cons a t ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem main : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∃ x4 ∈ x2.gates, x4.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ PEqualNP.MetaComplexity.Monotone2 x6 ∧ x5.size + x6.size + (1 : ℕ) = x2.size ∧ ∀ (x7 : Fin x1 → Bool), x2.eval (List.ofFn x7) = x6.eval (x5.wires (List.ofFn x7) ++ [!x5.eval (List.ofFn x7)]) := by
  intro n C hF hN
  obtain ⟨A, g, B, hC, hg, hB⟩ := split_last (fun x : Gate => x.op = GateOp.not) C.gates hN
  refine ⟨⟨A, g.inputs.headD (n + A.length)⟩, ⟨B, C.output⟩, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact hF a (by rw [hC]; simp [ha])
  · intro b hb
    have h1 := hF b (by rw [hC]; simp [hb])
    have h2 := hB b hb
    refine ⟨?_, h1.2⟩
    have h3 := h1.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h3 ⊢
    rcases h3 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h h2
  · simp only [Circuit.size, hC, List.length_append, List.length_cons]
    omega
  · intro x
    have hlen := len_foldl A (List.ofFn x)
    unfold Circuit.eval Circuit.wires
    simp only
    rw [hC, List.foldl_append, List.foldl_cons]
    generalize hW : List.foldl (fun w g => w ++ [g.op.eval (List.map (fun i => w.getD i false) g.inputs)]) (List.ofFn x) A = W at hlen ⊢
    have key : g.op.eval (List.map (fun i => W.getD i false) g.inputs)
        = !(W.getD (g.inputs.headD (n + A.length)) false) := by
      rw [hg]
      rcases hgi : g.inputs with _ | ⟨i, rest⟩
      · simp only [GateOp.eval, List.map_nil, List.headD_nil]
        rw [List.getD_eq_default]
        rw [hlen]
        simp
      · simp [GateOp.eval]
    rw [key]

end PEqualNP.Outside.L_meta_8295

theorem PEqualNP.Outside.L_meta_8295 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∃ x4 ∈ x2.gates, x4.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ PEqualNP.MetaComplexity.Monotone2 x6 ∧ x5.size + x6.size + (1 : ℕ) = x2.size ∧ ∀ (x7 : Fin x1 → Bool), x2.eval (List.ofFn x7) = x6.eval (x5.wires (List.ofFn x7) ++ [!x5.eval (List.ofFn x7)]) :=
  PEqualNP.Outside.L_meta_8295.main
