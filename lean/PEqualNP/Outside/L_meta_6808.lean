import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6808

open PEqualNP.CircuitLowerBounds

def Spec (x1 : ℕ) (x4 : ℕ → Set (Fin x1 → Bool)) (k : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 ∧ (∀ i ∈ g.inputs, i < x1 + k) ∧
  ∀ (x : Fin x1 → Bool) (w : List Bool), (∀ i < x1 + k, (w.getD i false = true ↔ x ∈ x4 i)) →
    (g.op.eval (g.inputs.map fun i => w.getD i false) = true ↔ x ∈ x4 (x1 + k))

theorem spec_exists (x1 : ℕ) (x4 : ℕ → Set (Fin x1 → Bool)) (k : ℕ)
    (h : ∃ (x8 : ℕ) (x9 : ℕ), Max.max x8 x9 < x1 + k ∧
      x4 (x1 + k) ∈ [x4 x8 ∪ x4 x9, x4 x8, ∅, x4 x8 ∩ x4 x9]) :
    ∃ g : Gate, Spec x1 x4 k g := by
  obtain ⟨a, b, hab, hmem⟩ := h
  have ha : a < x1 + k := lt_of_le_of_lt (le_max_left a b) hab
  have hb : b < x1 + k := lt_of_le_of_lt (le_max_right a b) hab
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h1 | h1 | h1 | h1
  · refine ⟨⟨GateOp.or, [a, b]⟩, Or.inr rfl, by simp, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> assumption
    · intro x w hw
      rw [h1]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id, Bool.or_eq_true, Set.mem_union]
      rw [hw a ha, hw b hb]
  · refine ⟨⟨GateOp.or, [a]⟩, Or.inr rfl, by simp, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl
      assumption
    · intro x w hw
      rw [h1]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id]
      rw [hw a ha]
  · refine ⟨⟨GateOp.or, []⟩, Or.inr rfl, by simp, ?_, ?_⟩
    · intro i hi
      simp at hi
    · intro x w _
      rw [h1]
      simp [GateOp.eval]
  · refine ⟨⟨GateOp.and, [a, b]⟩, Or.inl rfl, by simp, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> assumption
    · intro x w hw
      rw [h1]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        Bool.and_true, id, Bool.and_eq_true, Set.mem_inter_iff]
      rw [hw a ha, hw b hb]

theorem wires_spec (x1 : ℕ) (x4 : ℕ → Set (Fin x1 → Bool))
    (hin : ∀ (x5 : Fin x1), x4 ↑x5 = {x6 : Fin x1 → Bool | x6 x5 = Bool.true})
    (G : ℕ → Gate) (x2 : ℕ) (hG : ∀ k < x2, Spec x1 x4 k (G k)) (x : Fin x1 → Bool) :
    ∀ m ≤ x2,
      (((List.range m).map G).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn x)).length = x1 + m ∧
      ∀ i < x1 + m, ((((List.range m).map G).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn x)).getD i false = true ↔ x ∈ x4 i) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨by simp, ?_⟩
    intro i hi
    simp only [List.range_zero, List.map_nil, List.foldl_nil]
    have hi' : i < x1 := by omega
    rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_ofFn]
    have := hin ⟨i, hi'⟩
    simp only at this
    rw [this]
    rfl
  | succ m ih =>
    intro hm
    obtain ⟨hlen, hval⟩ := ih (by omega)
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    set w := ((List.range m).map G).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn x) with hw
    refine ⟨by simp [hlen]; omega, ?_⟩
    intro i hi
    by_cases hlt : i < x1 + m
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact hval i hlt
    · have hieq : i = x1 + m := by omega
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have h0 : i - w.length = 0 := by omega
      rw [h0]
      simp only [List.getD_cons_zero]
      rw [hieq]
      exact (hG m (by omega)).2.2.2 x w hval

end PEqualNP.Outside.L_meta_6808

theorem PEqualNP.Outside.L_meta_6808 : ∀ (x1 x2 x3 : ℕ) (x4 : ℕ → Set (Fin x1 → Bool)), (∀ (x5 : Fin x1), x4 ↑x5 = {x6 : Fin x1 → Bool | x6 x5 = Bool.true}) → (∀ x6 < x2, ∃ (x8 : ℕ) (x9 : ℕ), Max.max x8 x9 < x1 + x6 ∧ x4 (x1 + x6) ∈ [x4 x8 ∪ x4 x9, x4 x8, ∅, x4 x8 ∩ x4 x9]) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), x7.output = x3 ∧ x7.size = x2 ∧ PEqualNP.MetaComplexity.Monotone2 x7 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x7 ∧ ∀ x8 < x1 + x2, ∀ (x10 : Fin x1 → Bool), (x7.wires (List.ofFn x10)).getD x8 Bool.false = Bool.true ↔ x10 ∈ x4 x8 := by
  intro x1 x2 x3 x4 hin hstep
  have hex : ∀ k < x2, ∃ g : PEqualNP.CircuitLowerBounds.Gate,
      PEqualNP.Outside.L_meta_6808.Spec x1 x4 k g :=
    fun k hk => PEqualNP.Outside.L_meta_6808.spec_exists x1 x4 k (hstep k hk)
  classical
  let G : ℕ → PEqualNP.CircuitLowerBounds.Gate := fun k =>
    if h : k < x2 then Classical.choose (hex k h) else ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
  have hG : ∀ k < x2, PEqualNP.Outside.L_meta_6808.Spec x1 x4 k (G k) := by
    intro k hk
    simp only [G, dif_pos hk]
    exact Classical.choose_spec (hex k hk)
  refine ⟨⟨(List.range x2).map G, x3⟩, rfl, by simp [PEqualNP.CircuitLowerBounds.Circuit.size],
    ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map, List.mem_range] at hg
    obtain ⟨k, hk, rfl⟩ := hg
    obtain ⟨hop, hlen, _, _⟩ := hG k hk
    refine ⟨?_, hlen⟩
    rcases hop with h | h <;> simp [h]
  · intro j hj i hi
    simp only [List.length_map, List.length_range] at hj
    have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt
        ⟨(List.range x2).map G, x3⟩ j = G j := by
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
      rw [List.getD_eq_getElem _ _ (by simpa using hj)]
      simp
    rw [hgate] at hi
    exact (hG j hj).2.2.1 i hi
  · intro x8 hx8 x10
    exact (PEqualNP.Outside.L_meta_6808.wires_spec x1 x4 hin G x2 hG x10 x2 le_rfl).2 x8 hx8
