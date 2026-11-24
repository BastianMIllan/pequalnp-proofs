import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3574

-- gates of the list of size at least two inside X and not inside Z
def G {n : ℕ} (L : List (Finset (Fin n))) (X Z : Finset (Fin n)) : Finset (Fin L.length) :=
  Finset.univ.filter (fun i => 1 < (L.get i).card ∧ L.get i ⊆ X ∧ ¬ L.get i ⊆ Z)

theorem small_bound {n : ℕ} (P Z : Finset (Fin n)) (hP : P.card ≤ 1) :
    (P \ Z).card ≤ (if Disjoint P Z then 1 else 0) := by
  by_cases hd : Disjoint P Z
  · rw [if_pos hd]
    exact le_trans (Finset.card_le_card Finset.sdiff_subset) hP
  · rw [if_neg hd]
    rw [Finset.not_disjoint_iff] at hd
    obtain ⟨e, heP, heZ⟩ := hd
    have : P \ Z = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      rw [Finset.mem_sdiff] at hx
      have hxe : x = e := Finset.card_le_one.1 hP x hx.1 e heP
      exact hx.2 (hxe ▸ heZ)
    rw [this]
    simp

theorem main {n : ℕ} (L : List (Finset (Fin n)))
    (hL : ∀ (k : ℕ) (X : Finset (Fin n)), L[k]? = Option.some X → ∃ (A B : Finset (Fin n)),
      X = A ∪ B ∧ (A.card ≤ 1 ∨ A ∈ List.take k L) ∧ (B.card ≤ 1 ∨ B ∈ List.take k L)) :
    ∀ (k : ℕ) (X : Finset (Fin n)), L[k]? = Option.some X → ∀ Z : Finset (Fin n),
      (X \ Z).card ≤ (G L X Z).card + (if Disjoint X Z then 1 else 0) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro X hX Z
  -- bound for a piece
  have piece : ∀ (P : Finset (Fin n)), (P.card ≤ 1 ∨ P ∈ List.take k L) → ∀ Z' : Finset (Fin n),
      (P \ Z').card ≤ (G L P Z').card + (if Disjoint P Z' then 1 else 0) := by
    intro P hP Z'
    rcases hP with hP | hP
    · exact le_trans (small_bound P Z' hP) (Nat.le_add_left _ _)
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hP
      rw [List.getElem?_take] at hj
      split_ifs at hj with hjk
      · exact ih j hjk P hj Z'
  obtain ⟨A, B, hAB, hA, hB⟩ := hL k X hX
  by_cases hsmall : X.card ≤ 1
  · exact le_trans (small_bound X Z hsmall) (Nat.le_add_left _ _)
  push_neg at hsmall
  by_cases hXZ : X ⊆ Z
  · rw [Finset.sdiff_eq_empty_iff_subset.2 hXZ]
    simp
  by_cases hBA : B ⊆ A
  · have hXA : X = A := by rw [hAB]; exact Finset.union_eq_left.2 hBA
    subst hXA
    exact piece _ hA Z
  by_cases hAB' : A ⊆ B
  · have hXB : X = B := by rw [hAB]; exact Finset.union_eq_right.2 hAB'
    subst hXB
    exact piece _ hB Z
  obtain ⟨hk, hkX⟩ := List.getElem?_eq_some_iff.1 hX
  set k' : Fin L.length := ⟨k, hk⟩ with hk'
  have hgk : L.get k' = X := by simp [hk', hkX]
  have hAX : A ⊆ X := by rw [hAB]; exact Finset.subset_union_left
  have hBX : B ⊆ X := by rw [hAB]; exact Finset.subset_union_right
  have h1 := piece A hA Z
  have h2 := piece B hB (Z ∪ A)
  -- split X \ Z
  have hsplit : X \ Z ⊆ (A \ Z) ∪ (B \ (Z ∪ A)) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_union]
    have hx1 := hx.1
    rw [hAB, Finset.mem_union] at hx1
    by_cases hxA : x ∈ A
    · exact Or.inl ⟨hxA, hx.2⟩
    · rcases hx1 with h | h
      · exact absurd h hxA
      · exact Or.inr ⟨h, fun h' => h'.elim hx.2 hxA⟩
  have hc1 := le_trans (Finset.card_le_card hsplit) (Finset.card_union_le _ _)
  -- gates
  have hdisj : G L A Z ∩ G L B (Z ∪ A) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro i hi
    simp only [G, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi.2.2.2 (fun x hx => Finset.mem_union.2 (Or.inr (hi.1.2.1 hx)))
  have hsub : G L A Z ∪ G L B (Z ∪ A) ⊆ G L X Z := by
    intro i hi
    simp only [G, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rcases hi with hi | hi
    · exact ⟨hi.1, Finset.Subset.trans hi.2.1 hAX, hi.2.2⟩
    · refine ⟨hi.1, Finset.Subset.trans hi.2.1 hBX, ?_⟩
      intro hz
      exact hi.2.2 (fun x hx => Finset.mem_union.2 (Or.inl (hz hx)))
  have hss : G L A Z ∪ G L B (Z ∪ A) ⊂ G L X Z := by
    rw [Finset.ssubset_iff_of_subset hsub]
    refine ⟨k', ?_, ?_⟩
    · simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hgk]
      exact ⟨hsmall, Finset.Subset.refl _, hXZ⟩
    · simp only [G, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hgk]
      rintro (h | h)
      · exact hBA (Finset.Subset.trans hBX h.2.1)
      · exact hAB' (Finset.Subset.trans hAX h.2.1)
  have hc2 := Finset.card_lt_card hss
  have hc3 := Finset.card_union_add_card_inter (G L A Z) (G L B (Z ∪ A))
  rw [hdisj] at hc3
  simp only [Finset.card_empty, add_zero] at hc3
  have hind : (if Disjoint A Z then 1 else 0) + (if Disjoint B (Z ∪ A) then 1 else 0)
      ≤ 1 + (if Disjoint X Z then 1 else 0) := by
    by_cases d1 : Disjoint A Z
    · by_cases d2 : Disjoint B (Z ∪ A)
      · have d3 : Disjoint X Z := by
          rw [hAB]
          exact Finset.disjoint_union_left.2 ⟨d1, (Finset.disjoint_union_right.1 d2).1⟩
        simp [d1, d2, d3]
      · simp only [d1, d2, if_true, if_false]
        split_ifs <;> omega
    · simp only [d1, if_false]
      split_ifs <;> omega
  omega

end PEqualNP.Outside.L_meta_3574

theorem PEqualNP.Outside.L_meta_3574 : ∀ (x1 : ℕ) (x2 : List (Finset (Fin x1))), (∀ (x3 : ℕ) (x4 : Finset (Fin x1)), x2[x3]? = Option.some x4 → ∃ (x6 : Finset (Fin x1)) (x7 : Finset (Fin x1)), x4 = x6 ∪ x7 ∧ (x6.card ≤ (1 : ℕ) ∨ x6 ∈ List.take x3 x2) ∧ (x7.card ≤ (1 : ℕ) ∨ x7 ∈ List.take x3 x2)) → ∀ x4 ∈ x2, x4.card ≤ Fintype.card { x6 : Fin x2.length // (1 : ℕ) < (x2.get x6).card ∧ x2.get x6 ⊆ x4 } + (1 : ℕ) := by
  intro x1 L hL X hXL
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hXL
  have h := PEqualNP.Outside.L_meta_3574.main L hL k X hk ∅
  simp only [Finset.sdiff_empty, Finset.disjoint_empty_right, if_true] at h
  rw [Fintype.card_subtype]
  refine le_trans h (Nat.add_le_add_right (Finset.card_le_card ?_) 1)
  intro i hi
  simp only [PEqualNP.Outside.L_meta_3574.G, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨hi.1, hi.2.1⟩
