import Mathlib
import PEqualNP.Defs

-- Take the least wire that contains the point and misses the set. It is not an input, and it
-- cannot be a union, a copy or empty, since then an earlier wire would contain the point and
-- miss the set. So it is an intersection of two earlier wires, both meeting the set.
theorem PEqualNP.Outside.L_meta_6124 : ∀ (x1 : Type) (x2 x3 x4 : ℕ) (x5 : ℕ → Set x1) (x6 : Set x1), x4 < x2 + x3 → (∀ x8 < x2, ¬Disjoint (x5 x8) x6) → (∀ x9 < x3, ∃ x11 < x2 + x9, ∃ x12 < x2 + x9, x5 (x2 + x9) ∈ [x5 x11 ∪ x5 x12, x5 x11 ∩ x5 x12, x5 x11, ∅]) → Disjoint (x5 x4) x6 → ∀ x11 ∈ x5 x4, ∃ x13 < x3, ∃ x14 < x2 + x13, ∃ x15 < x2 + x13, x5 (x2 + x13) = x5 x14 ∩ x5 x15 ∧ ¬Disjoint (x5 x14) x6 ∧ ¬Disjoint (x5 x15) x6 ∧ Disjoint (x5 (x2 + x13)) x6 ∧ x11 ∈ x5 (x2 + x13) ∧ ∀ x16 < x2 + x13, x11 ∈ x5 x16 → ¬Disjoint (x5 x16) x6 := by
  intro α n m k s T hk hin hg hdk p hp
  classical
  have hex : ∃ w, p ∈ s w ∧ Disjoint (s w) T := ⟨k, hp, hdk⟩
  set w := Nat.find hex with hw
  have hwspec : p ∈ s w ∧ Disjoint (s w) T := Nat.find_spec hex
  have hmin : ∀ v < w, p ∈ s v → ¬Disjoint (s v) T := by
    intro v hv hpv hdv
    exact Nat.find_min hex hv ⟨hpv, hdv⟩
  have hwk : w ≤ k := Nat.find_min' hex ⟨hp, hdk⟩
  have hnw : n ≤ w := by
    by_contra h
    push_neg at h
    exact hin w h hwspec.2
  obtain ⟨j, hj⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hjm : j < m := by omega
  obtain ⟨a, ha, b, hb, hmem⟩ := hg j hjm
  rw [← hj] at ha hb hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · exfalso
    have hpw := hwspec.1
    rw [h] at hpw
    rcases hpw with hpa | hpb
    · apply hmin a ha hpa
      have hsub : s a ⊆ s w := by rw [h]; exact Set.subset_union_left
      exact Disjoint.mono_left hsub hwspec.2
    · apply hmin b hb hpb
      have hsub : s b ⊆ s w := by rw [h]; exact Set.subset_union_right
      exact Disjoint.mono_left hsub hwspec.2
  · have hpw := hwspec.1
    rw [h] at hpw
    refine ⟨j, hjm, a, ?_, b, ?_, ?_, hmin a ha hpw.1, hmin b hb hpw.2, ?_, ?_, ?_⟩
    · rw [← hj]; exact ha
    · rw [← hj]; exact hb
    · rw [← hj]; exact h
    · rw [← hj]; exact hwspec.2
    · rw [← hj]; exact hwspec.1
    · intro v hv hpv
      rw [← hj] at hv
      exact hmin v hv hpv
  · exfalso
    have hpw := hwspec.1
    rw [h] at hpw
    apply hmin a ha hpw
    rw [← h]
    exact hwspec.2
  · exfalso
    have hpw := hwspec.1
    rw [h] at hpw
    exact hpw
