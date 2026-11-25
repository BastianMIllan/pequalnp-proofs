import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6015

-- A wire only reads the choice bits of the gates at or below it.
theorem indep (n m : ℕ) (F : (Fin m → Bool) → ℕ → Finset ℕ)
    (hin : ∀ (c : Fin m → Bool), ∀ w < n, F c w = {w})
    (hg : ∀ (j : Fin m), ∃ a < n + ↑j, ∃ b < n + ↑j,
      (∀ (c : Fin m → Bool), F c (n + ↑j) = F c a ∪ F c b) ∨
      (∀ (c : Fin m → Bool), F c (n + ↑j) = if c j = Bool.true then F c a else F c b) ∨
      ∀ (c : Fin m → Bool), F c (n + ↑j) = ∅) :
    ∀ w, w < n + m → ∀ c c' : Fin m → Bool,
      (∀ j : Fin m, n + j.val ≤ w → c j = c' j) → F c w = F c' w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw c c' hag
    by_cases hlt : w < n
    · rw [hin c w hlt, hin c' w hlt]
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < m := by omega
      obtain ⟨a, ha, b, hb, h⟩ := hg ⟨k, hk⟩
      have ha' : a < n + k := ha
      have hb' : b < n + k := hb
      have hA : F c a = F c' a :=
        ih a (by omega) (by omega) c c' (fun j hj => hag j (by omega))
      have hB : F c b = F c' b :=
        ih b (by omega) (by omega) c c' (fun j hj => hag j (by omega))
      rcases h with h | h | h
      · rw [h c, h c', hA, hB]
      · rw [h c, h c', hA, hB, hag ⟨k, hk⟩ (le_refl _)]
      · rw [h c, h c']

theorem canon (n m : ℕ) (F : (Fin m → Bool) → ℕ → Finset ℕ)
    (hin : ∀ (c : Fin m → Bool), ∀ w < n, F c w = {w})
    (hg : ∀ (j : Fin m), ∃ a < n + ↑j, ∃ b < n + ↑j,
      (∀ (c : Fin m → Bool), F c (n + ↑j) = F c a ∪ F c b) ∨
      (∀ (c : Fin m → Bool), F c (n + ↑j) = if c j = Bool.true then F c a else F c b) ∨
      ∀ (c : Fin m → Bool), F c (n + ↑j) = ∅) (S : Set ℕ) :
    ∀ k, k ≤ m → ∃ c : Fin m → Bool, ∀ w < n + k,
      (∃ c' : Fin m → Bool, ∀ x ∈ F c' w, x ∈ S) → ∀ x ∈ F c w, x ∈ S := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun _ => Bool.true, fun w hw => ?_⟩
    rintro ⟨c', hc'⟩
    have hw' : w < n := by omega
    rw [hin _ w hw']
    rw [hin c' w hw'] at hc'
    exact hc'
  | succ k ih =>
    intro hkm
    obtain ⟨c, hc⟩ := ih (by omega)
    have hk : k < m := by omega
    obtain ⟨a, ha0, b, hb0, h⟩ := hg ⟨k, hk⟩
    have ha : a < n + k := ha0
    have hb : b < n + k := hb0
    let c1 : Fin m → Bool := fun i =>
      if i.val = k then (if (∀ x ∈ F c a, x ∈ S) then Bool.true else Bool.false) else c i
    have heq : ∀ w < n + k, F c1 w = F c w := by
      intro w hw
      apply indep n m F hin hg w (by omega) c1 c
      intro j hj
      have : j.val ≠ k := by omega
      simp only [c1, if_neg this]
    have hc1k : c1 ⟨k, hk⟩ = (if (∀ x ∈ F c a, x ∈ S) then Bool.true else Bool.false) := by
      simp only [c1, if_pos rfl]
    refine ⟨c1, fun w hw => ?_⟩
    by_cases hwk : w < n + k
    · rw [heq w hwk]
      exact hc w hwk
    · have hwe : w = n + k := by omega
      subst hwe
      rintro ⟨c', hc'⟩
      rcases h with h | h | h
      · rw [h c'] at hc'
        have hPa : ∀ x ∈ F c a, x ∈ S :=
          hc a ha ⟨c', fun x hx => hc' x (Finset.mem_union_left _ hx)⟩
        have hPb : ∀ x ∈ F c b, x ∈ S :=
          hc b hb ⟨c', fun x hx => hc' x (Finset.mem_union_right _ hx)⟩
        rw [h c1, heq a ha, heq b hb]
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact hPa x hx
        · exact hPb x hx
      · rw [h c'] at hc'
        rw [h c1, heq a ha, heq b hb, hc1k]
        by_cases hcj : c' ⟨k, hk⟩ = Bool.true
        · rw [if_pos hcj] at hc'
          have hPa : ∀ x ∈ F c a, x ∈ S := hc a ha ⟨c', hc'⟩
          rw [if_pos hPa, if_pos rfl]
          exact hPa
        · rw [if_neg hcj] at hc'
          have hPb : ∀ x ∈ F c b, x ∈ S := hc b hb ⟨c', hc'⟩
          by_cases hPa : ∀ x ∈ F c a, x ∈ S
          · rw [if_pos hPa, if_pos rfl]
            exact hPa
          · rw [if_neg hPa]
            simp only [Bool.false_eq_true, if_false]
            exact hPb
      · rw [h c1]
        intro x hx
        simp at hx

end PEqualNP.Outside.L_meta_6015

theorem PEqualNP.Outside.L_meta_6015 : ∀ (x1 x2 : ℕ) (x3 : (Fin x2 → Bool) → ℕ → Finset ℕ),   (∀ (x4 : Fin x2 → Bool), ∀ x5 < x1, x3 x4 x5 = {x5}) →     (∀ (x5 : Fin x2), ∃ x6 < x1 + ↑x5, ∃ x7 < x1 + ↑x5, (∀ (x8 : Fin x2 → Bool), x3 x8 (x1 + ↑x5) = x3 x8 x6 ∪ x3 x8 x7) ∨ (∀ (x8 : Fin x2 → Bool), x3 x8 (x1 + ↑x5) = if x8 x5 = Bool.true then x3 x8 x6 else x3 x8 x7) ∨ ∀ (x8 : Fin x2 → Bool), x3 x8 (x1 + ↑x5) = ∅) →       have x6 : ℕ → Set (Set ℕ) := fun (x6 : ℕ) => {x7 : Set ℕ | ∃ (x8 : Fin x2 → Bool), ∀ x9 ∈ x3 x8 x6, x9 ∈ x7};       ∀ (x7 : Fin x2), ∃ x8 < x1 + ↑x7, ∃ x9 < x1 + ↑x7, x6 (x1 + ↑x7) = x6 x8 ∩ x6 x9 ∨ x6 (x1 + ↑x7) = x6 x8 ∪ x6 x9 ∨ x6 (x1 + ↑x7) = Set.univ := by
  intro n m F hin hg
  classical
  dsimp only
  intro j
  obtain ⟨a, ha, b, hb, h⟩ := hg j
  have hjm : n + j.val < n + m := by have := j.2; omega
  refine ⟨a, ha, b, hb, ?_⟩
  rcases h with h | h | h
  · left
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨c, hc⟩
      rw [h c] at hc
      exact ⟨⟨c, fun x hx => hc x (Finset.mem_union_left _ hx)⟩,
        ⟨c, fun x hx => hc x (Finset.mem_union_right _ hx)⟩⟩
    · rintro ⟨hA, hB⟩
      obtain ⟨c, hc⟩ := PEqualNP.Outside.L_meta_6015.canon n m F hin hg S m (le_refl _)
      refine ⟨c, ?_⟩
      rw [h c]
      have hPa := hc a (by omega) hA
      have hPb := hc b (by omega) hB
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hPa x hx
      · exact hPb x hx
  · right; left
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨c, hc⟩
      rw [h c] at hc
      by_cases hcj : c j = Bool.true
      · rw [if_pos hcj] at hc
        exact Or.inl ⟨c, hc⟩
      · rw [if_neg hcj] at hc
        exact Or.inr ⟨c, hc⟩
    · rintro (⟨c, hc⟩ | ⟨c, hc⟩)
      · let c1 : Fin m → Bool := fun i => if i = j then Bool.true else c i
        have hag : ∀ i : Fin m, n + i.val ≤ a → c1 i = c i := by
          intro i hi
          have : i ≠ j := by intro e; subst e; omega
          simp only [c1, if_neg this]
        have hE := PEqualNP.Outside.L_meta_6015.indep n m F hin hg a (by omega) c1 c hag
        refine ⟨c1, ?_⟩
        rw [h c1]
        have : c1 j = Bool.true := by simp only [c1, if_pos rfl]
        rw [if_pos this, hE]
        exact hc
      · let c1 : Fin m → Bool := fun i => if i = j then Bool.false else c i
        have hag : ∀ i : Fin m, n + i.val ≤ b → c1 i = c i := by
          intro i hi
          have : i ≠ j := by intro e; subst e; omega
          simp only [c1, if_neg this]
        have hE := PEqualNP.Outside.L_meta_6015.indep n m F hin hg b (by omega) c1 c hag
        refine ⟨c1, ?_⟩
        rw [h c1]
        have : ¬ c1 j = Bool.true := by simp only [c1, if_pos rfl]; decide
        rw [if_neg this, hE]
        exact hc
  · right; right
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    refine ⟨fun _ => Bool.true, ?_⟩
    rw [h]
    intro x hx
    simp at hx
