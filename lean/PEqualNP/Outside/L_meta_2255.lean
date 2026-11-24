import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2255

open PEqualNP.CircuitLowerBounds

def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len_fold (gs : List Gate) (x : List Bool) :
    (gs.foldl F x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, F, List.length_append, List.length_cons, List.length_nil]
    omega

theorem getD_snoc (l : List Bool) (v : Bool) (w : ℕ) :
    (l ++ [v]).getD w false =
      if w < l.length then l.getD w false else if w = l.length then v else false := by
  rcases lt_trichotomy w l.length with h | h | h
  · rw [if_pos h, List.getD_append _ _ _ _ h]
  · subst h
    simp
  · rw [if_neg (by omega), if_neg (by omega), List.getD_eq_default _ _ (by simp; omega)]

theorem key (n : ℕ) (gs : List Gate) : (∀ g ∈ gs, g.inputs.length ≤ 2) → ∀ T : Finset ℕ,
    ∃ S : Finset ℕ, S.card ≤ T.card + gs.length ∧ (∀ s ∈ S, s < n) ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ s ∈ S, x.getD s false = y.getD s false) →
          ∀ w ∈ T, (gs.foldl F x).getD w false = (gs.foldl F y).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ T
    refine ⟨T.filter (· < n), ?_, ?_, ?_⟩
    · simpa using Finset.card_filter_le T _
    · intro s hs
      exact (Finset.mem_filter.1 hs).2
    · intro x y hx hy hS w hw
      simp only [List.foldl_nil]
      by_cases h : w < n
      · exact hS w (Finset.mem_filter.2 ⟨hw, h⟩)
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | append_singleton gs g ih =>
    intro hg T
    have hg1 : ∀ g' ∈ gs, g'.inputs.length ≤ 2 := fun g' h => hg g' (List.mem_append_left _ h)
    have hg2 : g.inputs.length ≤ 2 := hg g (List.mem_append_right _ (List.mem_singleton_self _))
    by_cases hm : n + gs.length ∈ T
    · obtain ⟨S, hc, hlt, hag⟩ := ih hg1 (T.filter (· < n + gs.length) ∪ g.inputs.toFinset)
      have h1 : (T.filter (· < n + gs.length)).card < T.card :=
        Finset.card_lt_card (Finset.filter_ssubset.2 ⟨n + gs.length, hm, lt_irrefl _⟩)
      have h2 := Finset.card_union_le (T.filter (· < n + gs.length)) g.inputs.toFinset
      have h3 := List.toFinset_card_le g.inputs
      refine ⟨S, ?_, hlt, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro x y hx hy hS w hw
        have hlx := len_fold gs x
        have hly := len_fold gs y
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, F]
        rw [getD_snoc, getD_snoc, hlx, hly, hx, hy]
        split_ifs with ha hb
        · exact hag x y hx hy hS w (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hw, ha⟩))
        · congr 1
          apply List.map_congr_left
          intro i hi
          exact hag x y hx hy hS i (Finset.mem_union_right _ (List.mem_toFinset.2 hi))
        · rfl
    · obtain ⟨S, hc, hlt, hag⟩ := ih hg1 (T.filter (· < n + gs.length))
      have h1 := Finset.card_filter_le T (· < n + gs.length)
      refine ⟨S, ?_, hlt, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro x y hx hy hS w hw
        have hlx := len_fold gs x
        have hly := len_fold gs y
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, F]
        rw [getD_snoc, getD_snoc, hlx, hly, hx, hy]
        split_ifs with ha hb
        · exact hag x y hx hy hS w (Finset.mem_filter.2 ⟨hw, ha⟩)
        · exact absurd (hb ▸ hw) hm
        · rfl

def p (j : Fin 6) : Fin 6 := if j.val < 2 then 2 else 0

def X (j : Fin 6) : Fin 6 → Bool := fun k => decide (k = j) || decide (k = p j)

def Y (j : Fin 6) : Fin 6 → Bool := fun k => decide (k = p j)

theorem fX : ∀ j : Fin 6, (fun z : Fin 6 → Bool => (z 0 && z 2) || (z 0 && z 3) || (z 0 && z 4) || (z 0 && z 5) || (z 1 && z 2) || (z 1 && z 3) || (z 1 && z 4) || (z 1 && z 5)) (X j) = true := by
  decide

theorem fY : ∀ j : Fin 6, (fun z : Fin 6 → Bool => (z 0 && z 2) || (z 0 && z 3) || (z 0 && z 4) || (z 0 && z 5) || (z 1 && z 2) || (z 1 && z 3) || (z 1 && z 4) || (z 1 && z 5)) (Y j) = false := by
  decide

theorem agree : ∀ j s : Fin 6, s ≠ j →
    (List.ofFn (X j)).getD s false = (List.ofFn (Y j)).getD s false := by
  decide

end PEqualNP.Outside.L_meta_2255

theorem PEqualNP.Outside.L_meta_2255 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun z : Fin 6 → Bool => (z 0 && z 2) || (z 0 && z 3) || (z 0 && z 4) || (z 0 && z 5) || (z 1 && z 2) || (z 1 && z 3) || (z 1 && z 4) || (z 1 && z 5)) x) → 5 ≤ C.size := by
  intro C hm _ hf
  by_contra hlt
  have hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g h => (hm g h).2
  obtain ⟨S, hc, hS6, hag⟩ := PEqualNP.Outside.L_meta_2255.key 6 C.gates hg {C.output}
  have hsz : C.gates.length < 5 := by
    simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hlt
    omega
  rw [Finset.card_singleton] at hc
  obtain ⟨i, hi6, hiS⟩ : ∃ i, i < 6 ∧ i ∉ S := by
    by_contra h
    push_neg at h
    have hsub : Finset.range 6 ⊆ S := fun i hi => h i (Finset.mem_range.1 hi)
    have := Finset.card_le_card hsub
    simp only [Finset.card_range] at this
    omega
  have e := hag (List.ofFn (PEqualNP.Outside.L_meta_2255.X ⟨i, hi6⟩))
    (List.ofFn (PEqualNP.Outside.L_meta_2255.Y ⟨i, hi6⟩)) (by simp) (by simp)
    (fun s hs => PEqualNP.Outside.L_meta_2255.agree ⟨i, hi6⟩ ⟨s, hS6 s hs⟩
      (fun h => hiS (by rw [← Fin.mk.inj_iff.1 h]; exact hs)))
    C.output (Finset.mem_singleton_self _)
  have hx : (C.gates.foldl PEqualNP.Outside.L_meta_2255.F
      (List.ofFn (PEqualNP.Outside.L_meta_2255.X ⟨i, hi6⟩))).getD C.output false = true := by
    have := hf (PEqualNP.Outside.L_meta_2255.X ⟨i, hi6⟩)
    rw [PEqualNP.Outside.L_meta_2255.fX] at this
    exact this
  have hy : (C.gates.foldl PEqualNP.Outside.L_meta_2255.F
      (List.ofFn (PEqualNP.Outside.L_meta_2255.Y ⟨i, hi6⟩))).getD C.output false = false := by
    have := hf (PEqualNP.Outside.L_meta_2255.Y ⟨i, hi6⟩)
    rw [PEqualNP.Outside.L_meta_2255.fY] at this
    exact this
  rw [hx, hy] at e
  exact Bool.noConfusion e
