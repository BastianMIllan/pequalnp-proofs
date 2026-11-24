import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2233

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open Classical

theorem getD_app_lt {α : Type} (l l' : List α) (z : α) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i z = l.getD i z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_self {α : Type} (l : List α) (v z : α) : (l ++ [v]).getD l.length z = v := by
  simp [List.getD_eq_getElem?_getD]

theorem orStep_length (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (orStep n cs g).length = cs.length + 1 := by
  unfold orStep; simp

theorem orStep_getD (n : ℕ) (cs : List (List ℕ)) (g : Gate) (i : ℕ) (h : i < cs.length) :
    (orStep n cs g).getD i [] = cs.getD i [] := by
  unfold orStep; exact getD_app_lt _ _ _ _ h

theorem orStep_last_or (n : ℕ) (cs : List (List ℕ)) (g : Gate) (hg : g.op = GateOp.or) :
    (orStep n cs g).getD cs.length [] = cs.length ::
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) []) := by
  unfold orStep; rw [if_pos hg, getD_app_self]

theorem orStep_last_nor (n : ℕ) (cs : List (List ℕ)) (g : Gate) (hg : ¬ g.op = GateOp.or) :
    (orStep n cs g).getD cs.length [] = [cs.length] := by
  unfold orStep; rw [if_neg hg, getD_app_self]

theorem T_length (n : ℕ) (gs : List Gate) :
    ∀ cs : List (List ℕ), (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs with
  | nil => intro cs; simp
  | cons g gs ih => intro cs; rw [List.foldl_cons, ih, orStep_length]; simp; omega

theorem T_getD (n : ℕ) (gs : List Gate) :
    ∀ (cs : List (List ℕ)) (i : ℕ), i < cs.length → (gs.foldl (orStep n) cs).getD i [] = cs.getD i [] := by
  induction gs with
  | nil => intro cs i _; rfl
  | cons g gs ih =>
    intro cs i hi
    rw [List.foldl_cons, ih _ _ (by rw [orStep_length]; omega), orStep_getD _ _ _ _ hi]

-- the OR closure of gate k
def cl (n : ℕ) (C : Circuit) (k : ℕ) : List ℕ := (orSets n C).getD k []

theorem orSets_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  unfold orSets; rw [T_length]; simp

theorem cl_split (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    ∃ P : List (List ℕ), P.length = k ∧ (∀ i < k, P.getD i [] = cl n C i) ∧
      cl n C k = (orStep n P (gateAt C k)).getD k [] := by
  have hg : gateAt C k = C.gates[k] := List.getD_eq_getElem _ _ hk
  set P := (C.gates.take k).foldl (orStep n) [] with hP
  have hPl : P.length = k := by rw [hP, T_length, List.length_take]; simp; omega
  have hsplit : orSets n C = (C.gates.drop k).foldl (orStep n) P := by
    rw [hP, ← List.foldl_append, List.take_append_drop]; rfl
  have hdrop : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := by
    rw [List.drop_eq_getElem_cons hk]
  refine ⟨P, hPl, ?_, ?_⟩
  · intro i hi
    unfold cl
    rw [hsplit]; exact (T_getD n _ P i (by omega)).symm
  · unfold cl
    rw [hsplit, hdrop, List.foldl_cons, T_getD n (C.gates.drop (k + 1)) (orStep n P C.gates[k]) k (by rw [orStep_length]; omega), hg]

theorem mem_cl_or (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hor : (gateAt C k).op = GateOp.or) (g : ℕ) :
    g ∈ cl n C k ↔ g = k ∨ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ g ∈ cl n C (w - n) := by
  obtain ⟨P, hPl, hPg, hcl⟩ := cl_split n C k hk
  rw [hcl]
  have e := orStep_last_or n P (gateAt C k) hor
  rw [hPl] at e
  rw [e, List.mem_cons, List.mem_flatMap]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨w, hw, hgw⟩
    rw [List.mem_filter, decide_eq_true_eq] at hw
    refine ⟨w, hw.1, hw.2.1, hw.2.2, ?_⟩
    rw [← hPg _ (by omega)]; exact hgw
  · rintro ⟨w, hw, h1, h2, hgw⟩
    refine ⟨w, ?_, ?_⟩
    · rw [List.mem_filter, decide_eq_true_eq]; exact ⟨hw, h1, h2⟩
    · rw [hPg _ (by omega)]; exact hgw

theorem cl_nor (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hor : ¬ (gateAt C k).op = GateOp.or) : cl n C k = [k] := by
  obtain ⟨P, hPl, _, hcl⟩ := cl_split n C k hk
  rw [hcl]
  have e := orStep_last_nor n P (gateAt C k) hor
  rw [hPl] at e
  exact e

theorem cl_ge (n : ℕ) (C : Circuit) (k : ℕ) (hk : C.gates.length ≤ k) : cl n C k = [] := by
  unfold cl
  apply List.getD_eq_default
  rw [orSets_length]; exact hk

theorem cl_le (n : ℕ) (C : Circuit) : ∀ k g, g ∈ cl n C k → g ≤ k ∧ g < C.gates.length := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro g hg
    by_cases hk : k < C.gates.length
    · by_cases hor : (gateAt C k).op = GateOp.or
      · rcases (mem_cl_or n C k hk hor g).1 hg with rfl | ⟨w, _, h1, h2, hgw⟩
        · exact ⟨le_refl _, hk⟩
        · have := ih (w - n) (by omega) g hgw
          exact ⟨by omega, this.2⟩
      · rw [cl_nor n C k hk hor] at hg
        simp at hg
        subst hg
        exact ⟨le_refl _, hk⟩
    · rw [cl_ge n C k (by omega)] at hg
      simp at hg

noncomputable def AS (n : ℕ) (C : Circuit) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter
    (fun g => (gateAt C g).op = GateOp.and ∧ ∃ s ∈ S, g ∈ cl n C s)

noncomputable def OS (n : ℕ) (C : Circuit) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter
    (fun g => (gateAt C g).op = GateOp.or ∧ ∃ s ∈ S, g ∈ cl n C s)

theorem main_count (n : ℕ) (C : Circuit)
    (hAO : ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length = 2) :
    ∀ B (S : Finset ℕ), (∀ s ∈ S, s < B) → (AS n C S).card ≤ (OS n C S).card + S.card := by
  intro B
  induction B with
  | zero =>
    intro S hS
    have : S = ∅ := by
      ext s; simp only [Finset.notMem_empty, iff_false]; intro hs; have := hS s hs; omega
    subst this
    simp [AS]
  | succ B ih =>
    intro S hS
    by_cases hB : B ∈ S
    · set S0 := S.erase B with hS0
      have hS0lt : ∀ s ∈ S0, s < B := by
        intro s hs
        rw [hS0, Finset.mem_erase] at hs
        have := hS s hs.2; omega
      have hcard : S.card = S0.card + 1 := by
        rw [hS0, Finset.card_erase_of_mem hB]
        have := Finset.card_pos.2 ⟨B, hB⟩
        omega
      have hmemS : ∀ s, s ∈ S ↔ s = B ∨ s ∈ S0 := by
        intro s; rw [hS0, Finset.mem_erase]
        constructor
        · intro hs; by_cases h : s = B
          · exact Or.inl h
          · exact Or.inr ⟨h, hs⟩
        · rintro (rfl | ⟨_, hs⟩)
          · exact hB
          · exact hs
      by_cases hk : B < C.gates.length
      · by_cases hor : (gateAt C B).op = GateOp.or
        · -- replace B by its gate inputs
          set W := (((gateAt C B).inputs.filter (fun w => decide (n ≤ w ∧ w < n + B))).toFinset).image
            (fun w => w - n) with hW
          set S' := S0 ∪ W with hS'
          have hWcard : W.card ≤ 2 := by
            rw [hW]
            refine le_trans Finset.card_image_le (le_trans (List.toFinset_card_le _) ?_)
            rw [← (hAO B hk).2]
            exact List.length_filter_le _ _
          have hS'lt : ∀ s ∈ S', s < B := by
            intro s hs
            rw [hS', Finset.mem_union] at hs
            rcases hs with hs | hs
            · exact hS0lt s hs
            · rw [hW, Finset.mem_image] at hs
              obtain ⟨w, hw, rfl⟩ := hs
              rw [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hw
              omega
          have hS'card : S'.card ≤ S0.card + 2 := by
            rw [hS']
            exact le_trans (Finset.card_union_le _ _) (by omega)
          have hih := ih S' hS'lt
          -- closure of S is closure of S' plus B
          have hcl : ∀ g, (∃ s ∈ S, g ∈ cl n C s) ↔ g = B ∨ ∃ s ∈ S', g ∈ cl n C s := by
            intro g
            constructor
            · rintro ⟨s, hs, hgs⟩
              rcases (hmemS s).1 hs with rfl | hs0
              · rcases (mem_cl_or n C s hk hor g).1 hgs with h | ⟨w, hw, h1, h2, hgw⟩
                · exact Or.inl h
                · refine Or.inr ⟨w - n, ?_, hgw⟩
                  rw [hS', Finset.mem_union]; right
                  rw [hW, Finset.mem_image]
                  refine ⟨w, ?_, rfl⟩
                  rw [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
                  exact ⟨hw, h1, h2⟩
              · exact Or.inr ⟨s, by rw [hS', Finset.mem_union]; exact Or.inl hs0, hgs⟩
            · rintro (rfl | ⟨s, hs, hgs⟩)
              · exact ⟨g, hB, (mem_cl_or n C g hk hor g).2 (Or.inl rfl)⟩
              · rw [hS', Finset.mem_union] at hs
                rcases hs with hs | hs
                · exact ⟨s, (hmemS s).2 (Or.inr hs), hgs⟩
                · rw [hW, Finset.mem_image] at hs
                  obtain ⟨w, hw, rfl⟩ := hs
                  rw [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hw
                  exact ⟨B, hB, (mem_cl_or n C B hk hor g).2 (Or.inr ⟨w, hw.1, hw.2.1, hw.2.2, hgs⟩)⟩
          have hA : AS n C S ⊆ AS n C S' := by
            intro g hg
            simp only [AS, Finset.mem_filter] at hg ⊢
            refine ⟨hg.1, hg.2.1, ?_⟩
            rcases (hcl g).1 hg.2.2 with rfl | h
            · rw [hor] at hg; exact absurd hg.2.1 (by intro h; cases h)
            · exact h
          have hBnot : B ∉ OS n C S' := by
            intro h
            simp only [OS, Finset.mem_filter] at h
            obtain ⟨s, hs, hBs⟩ := h.2.2
            have := (cl_le n C s B hBs).1
            have := hS'lt s hs
            omega
          have hO : insert B (OS n C S') ⊆ OS n C S := by
            intro g hg
            rw [Finset.mem_insert] at hg
            simp only [OS, Finset.mem_filter, Finset.mem_range]
            rcases hg with rfl | hg
            · exact ⟨hk, hor, (hcl g).2 (Or.inl rfl)⟩
            · simp only [OS, Finset.mem_filter, Finset.mem_range] at hg
              exact ⟨hg.1, hg.2.1, (hcl g).2 (Or.inr hg.2.2)⟩
          have h1 := Finset.card_le_card hA
          have h2 := Finset.card_le_card hO
          rw [Finset.card_insert_of_notMem hBnot] at h2
          omega
        · -- B is an AND gate: its closure is itself
          have hih := ih S0 hS0lt
          have hclB : cl n C B = [B] := cl_nor n C B hk hor
          have hA : AS n C S ⊆ insert B (AS n C S0) := by
            intro g hg
            rw [Finset.mem_insert]
            simp only [AS, Finset.mem_filter] at hg ⊢
            obtain ⟨s, hs, hgs⟩ := hg.2.2
            rcases (hmemS s).1 hs with rfl | hs0
            · rw [hclB] at hgs; simp at hgs; exact Or.inl hgs
            · exact Or.inr ⟨hg.1, hg.2.1, s, hs0, hgs⟩
          have hO : OS n C S0 ⊆ OS n C S := by
            intro g hg
            simp only [OS, Finset.mem_filter] at hg ⊢
            obtain ⟨s, hs, hgs⟩ := hg.2.2
            exact ⟨hg.1, hg.2.1, s, (hmemS s).2 (Or.inr hs), hgs⟩
          have h1 := le_trans (Finset.card_le_card hA) (Finset.card_insert_le _ _)
          have h2 := Finset.card_le_card hO
          omega
      · -- B is not a gate: its closure is empty
        have hih := ih S0 hS0lt
        have hclB : cl n C B = [] := cl_ge n C B (by omega)
        have hA : AS n C S ⊆ AS n C S0 := by
          intro g hg
          simp only [AS, Finset.mem_filter] at hg ⊢
          obtain ⟨s, hs, hgs⟩ := hg.2.2
          rcases (hmemS s).1 hs with rfl | hs0
          · rw [hclB] at hgs; simp at hgs
          · exact ⟨hg.1, hg.2.1, s, hs0, hgs⟩
        have hO : OS n C S0 ⊆ OS n C S := by
          intro g hg
          simp only [OS, Finset.mem_filter] at hg ⊢
          obtain ⟨s, hs, hgs⟩ := hg.2.2
          exact ⟨hg.1, hg.2.1, s, (hmemS s).2 (Or.inr hs), hgs⟩
        have h1 := Finset.card_le_card hA
        have h2 := Finset.card_le_card hO
        omega
    · apply ih S
      intro s hs
      have := hS s hs
      have : s ≠ B := fun h => hB (h ▸ hs)
      omega

end PEqualNP.Outside.L_meta_2233

open PEqualNP.Outside.L_meta_2233 in
theorem PEqualNP.Outside.L_meta_2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  classical
  intro n C F hAO hF
  by_cases hFe : F = ∅
  · subst hFe; simp
  obtain ⟨j0, hj0⟩ := Finset.nonempty_iff_ne_empty.2 hFe
  have hn : n ≤ C.output := (hF j0 hj0).2.2.1
  have hAO' : ∀ k < C.gates.length, ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.length = 2 := by
    intro k hk
    have hg : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := List.getD_eq_getElem _ _ hk
    rw [hg]
    exact ⟨hAO.1 _ (List.getElem_mem hk), hAO.2.2 _ (List.getElem_mem hk)⟩
  have hc := main_count n C hAO' (C.output - n + 1) {C.output - n} (by intro s hs; simp at hs; omega)
  have hFA : F ⊆ AS n C {C.output - n} := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := hF j hj
    simp only [AS, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, exists_eq_left]
    exact ⟨h1, h2, h3.2⟩
  have hset : {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} = ↑(OS n C {C.output - n}) := by
    ext i
    simp only [Set.mem_setOf_eq, OS, Finset.coe_filter, Finset.mem_range, Finset.mem_singleton,
      exists_eq_left, PEqualNP.CleanedNonEdge.OrReaches, cl]
    constructor
    · rintro ⟨h1, h2, _, h4⟩; exact ⟨h1, h2, h4⟩
    · rintro ⟨h1, h2, h4⟩; exact ⟨h1, h2, hn, h4⟩
  rw [hset, Set.ncard_coe_finset]
  have := Finset.card_le_card hFA
  simp only [Finset.card_singleton] at hc
  omega
