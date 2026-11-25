import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7606

def Good {α : Type} (x2 : ℕ) (x5 : ℕ → Set α) (L : List ℕ) : Prop :=
  ∀ (i : ℕ) (hi : i < L.length),
    (∀ x13 ∈ List.range x2 ++ List.take i L, x13 < L[i]) ∧ x5 L[i] ≠ ∅ ∧
      x5 L[i] ∉ List.map x5 (List.range x2 ++ List.take i L) ∧
      ∃ x13 ∈ List.map x5 (List.range x2 ++ List.take i L),
        ∃ x14 ∈ List.map x5 (List.range x2 ++ List.take i L),
          ¬x13 ⊆ x14 ∧ ¬x14 ⊆ x13 ∧ (x5 L[i] = x13 ∪ x14 ∨ x5 L[i] = x13 ∩ x14)

theorem good_nil {α : Type} (x2 : ℕ) (x5 : ℕ → Set α) : Good x2 x5 [] := by
  intro i hi
  simp at hi

theorem good_snoc {α : Type} (x2 : ℕ) (x5 : ℕ → Set α) (L : List ℕ) (v : ℕ)
    (hG : Good x2 x5 L) (hv : ∀ x ∈ List.range x2 ++ L, x < v) (hne : x5 v ≠ ∅)
    (hnot : x5 v ∉ List.map x5 (List.range x2 ++ L))
    (hex : ∃ A ∈ List.map x5 (List.range x2 ++ L), ∃ B ∈ List.map x5 (List.range x2 ++ L),
      ¬A ⊆ B ∧ ¬B ⊆ A ∧ (x5 v = A ∪ B ∨ x5 v = A ∩ B)) :
    Good x2 x5 (L ++ [v]) := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
  · have e1 : (L ++ [v])[i] = L[i] := List.getElem_append_left h
    have e2 : List.take i (L ++ [v]) = List.take i L := List.take_append_of_le_length h.le
    rw [e1, e2]
    exact hG i h
  · subst h
    have e1 : (L ++ [v])[L.length] = v := by simp
    have e2 : List.take L.length (L ++ [v]) = L := by simp
    rw [e1, e2]
    exact ⟨hv, hne, hnot, hex⟩

theorem main {α : Type} (x2 : ℕ) (x5 : ℕ → Set α) (x3 : ℕ)
    (h : ∀ x8 < x3, ∃ (x10 : ℕ) (x11 : ℕ), Max.max x10 x11 < x2 + x8 ∧
      x5 (x2 + x8) ∈ [x5 x10 ∪ x5 x11, x5 x10, ∅, x5 x10 ∩ x5 x11]) :
    ∀ k ≤ x3, ∃ L : List ℕ, L.length ≤ k ∧ (∀ v ∈ L, x2 ≤ v ∧ v < x2 + k) ∧ Good x2 x5 L ∧
      ∀ j < x2 + k, x5 j = ∅ ∨ x5 j ∈ List.map x5 (List.range x2 ++ L) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[], by simp, by simp, good_nil x2 x5, ?_⟩
    intro j hj
    right
    simp only [List.append_nil, List.mem_map, List.mem_range]
    exact ⟨j, by omega, rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨L, hlen, hrange, hG, hinv⟩ := ih (by omega)
    obtain ⟨a, b, hab, hS⟩ := h k (by omega)
    have ha : x5 a = ∅ ∨ x5 a ∈ List.map x5 (List.range x2 ++ L) :=
      hinv a (lt_of_le_of_lt (le_max_left a b) hab)
    have hb : x5 b = ∅ ∨ x5 b ∈ List.map x5 (List.range x2 ++ L) :=
      hinv b (lt_of_le_of_lt (le_max_right a b) hab)
    have key : x5 (x2 + k) = ∅ ∨ x5 (x2 + k) ∈ List.map x5 (List.range x2 ++ L) ∨
        ∃ A ∈ List.map x5 (List.range x2 ++ L), ∃ B ∈ List.map x5 (List.range x2 ++ L),
          ¬A ⊆ B ∧ ¬B ⊆ A ∧ (x5 (x2 + k) = A ∪ B ∨ x5 (x2 + k) = A ∩ B) := by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hS
      rcases hS with hS | hS | hS | hS
      · rcases ha with ha | ha
        · rw [hS, ha, Set.empty_union]
          exact hb.elim Or.inl (fun h => Or.inr (Or.inl h))
        rcases hb with hb | hb
        · rw [hS, hb, Set.union_empty]
          exact Or.inr (Or.inl ha)
        by_cases h1 : x5 a ⊆ x5 b
        · have e : x5 a ∪ x5 b = x5 b := sup_eq_right.mpr h1
          rw [hS, e]
          exact Or.inr (Or.inl hb)
        by_cases h2 : x5 b ⊆ x5 a
        · have e : x5 a ∪ x5 b = x5 a := sup_eq_left.mpr h2
          rw [hS, e]
          exact Or.inr (Or.inl ha)
        exact Or.inr (Or.inr ⟨_, ha, _, hb, h1, h2, Or.inl hS⟩)
      · rw [hS]
        exact ha.elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact Or.inl hS
      · rcases ha with ha | ha
        · rw [hS, ha, Set.empty_inter]
          exact Or.inl rfl
        rcases hb with hb | hb
        · rw [hS, hb, Set.inter_empty]
          exact Or.inl rfl
        by_cases h1 : x5 a ⊆ x5 b
        · have e : x5 a ∩ x5 b = x5 a := inf_eq_left.mpr h1
          rw [hS, e]
          exact Or.inr (Or.inl ha)
        by_cases h2 : x5 b ⊆ x5 a
        · have e : x5 a ∩ x5 b = x5 b := inf_eq_right.mpr h2
          rw [hS, e]
          exact Or.inr (Or.inl hb)
        exact Or.inr (Or.inr ⟨_, ha, _, hb, h1, h2, Or.inr hS⟩)
    by_cases hkeep : x5 (x2 + k) = ∅ ∨ x5 (x2 + k) ∈ List.map x5 (List.range x2 ++ L)
    · refine ⟨L, by omega, fun v hv => ⟨(hrange v hv).1, by have := (hrange v hv).2; omega⟩,
        hG, ?_⟩
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp (show j < (x2 + k).succ by omega) with hj' | hj'
      · exact hinv j hj'
      · subst hj'
        exact hkeep
    · have hnew : ∃ A ∈ List.map x5 (List.range x2 ++ L), ∃ B ∈ List.map x5 (List.range x2 ++ L),
          ¬A ⊆ B ∧ ¬B ⊆ A ∧ (x5 (x2 + k) = A ∪ B ∨ x5 (x2 + k) = A ∩ B) := by
        rcases key with h0 | h0 | h0
        · exact absurd (Or.inl h0) hkeep
        · exact absurd (Or.inr h0) hkeep
        · exact h0
      have hne : x5 (x2 + k) ≠ ∅ := fun h0 => hkeep (Or.inl h0)
      have hnot : x5 (x2 + k) ∉ List.map x5 (List.range x2 ++ L) := fun h0 => hkeep (Or.inr h0)
      have hmono : ∀ s, s ∈ List.map x5 (List.range x2 ++ L) →
          s ∈ List.map x5 (List.range x2 ++ (L ++ [x2 + k])) := by
        intro s hs
        simp only [List.mem_map, List.mem_append] at hs ⊢
        obtain ⟨j, hj, rfl⟩ := hs
        exact ⟨j, by tauto, rfl⟩
      refine ⟨L ++ [x2 + k], ?_, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro v hv
        simp only [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | hv
        · have := hrange v hv
          omega
        · omega
      · apply good_snoc x2 x5 L (x2 + k) hG _ hne hnot hnew
        intro x hx
        simp only [List.mem_append, List.mem_range] at hx
        rcases hx with hx | hx
        · omega
        · have := hrange x hx
          omega
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp (show j < (x2 + k).succ by omega) with hj' | hj'
        · rcases hinv j hj' with h0 | h0
          · exact Or.inl h0
          · exact Or.inr (hmono _ h0)
        · subst hj'
          right
          exact List.mem_map_of_mem (by simp)

end PEqualNP.Outside.L_meta_7606

theorem PEqualNP.Outside.L_meta_7606 : ∀ (x1 : Type) (x2 x3 x4 : ℕ) (x5 : ℕ → Set x1),   x4 < x2 + x3 →     x5 x4 ≠ ∅ →       (∀ x8 < x3, ∃ (x10 : ℕ) (x11 : ℕ), Max.max x10 x11 < x2 + x8 ∧ x5 (x2 + x8) ∈ [x5 x10 ∪ x5 x11, x5 x10, ∅, x5 x10 ∩ x5 x11]) →         ∃ (x9 : List ℕ),           x9.length ≤ x3 ∧             (∀ x10 ∈ x9, x2 ≤ x10 ∧ x10 < x2 + x3) ∧               x5 x4 ∈ List.map x5 (List.range x2 ++ x9) ∧                 ∀ (x10 : Fin x9.length),                   have x11 : List ℕ := List.range x2 ++ List.take (↑x10) x9;                   have x12 : Set x1 := x5 (x9.get x10);                   (∀ x13 ∈ x11, x13 < x9.get x10) ∧ x12 ≠ ∅ ∧ x12 ∉ List.map x5 x11 ∧ ∃ x13 ∈ List.map x5 x11, ∃ x14 ∈ List.map x5 x11, ¬x13 ⊆ x14 ∧ ¬x14 ⊆ x13 ∧ (x12 = x13 ∪ x14 ∨ x12 = x13 ∩ x14) := by
  intro x1 x2 x3 x4 x5 h4 hne h
  obtain ⟨L, hlen, hrange, hG, hinv⟩ := PEqualNP.Outside.L_meta_7606.main x2 x5 x3 h x3 le_rfl
  refine ⟨L, hlen, hrange, ?_, ?_⟩
  · rcases hinv x4 h4 with h0 | h0
    · exact absurd h0 hne
    · exact h0
  · intro i
    exact hG i.1 i.2
