import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_6726 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x1)) (x4 : Fin x1 × Fin x1 → Finset (Fin x2)), (44 : ℕ) * (x3.biUnion x4).card < x3.card → ∃ x6 ⊆ x3, x6.card = (44 : ℕ) * (x6.biUnion x4).card + (1 : ℕ) ∧ ∀ x7 ∈ x6.biUnion x4, (45 : ℕ) ≤ {x9 ∈ x6 | x7 ∈ x4 x9}.card := by
  intro x1 x2 x3 x4 h
  -- take a smallest subset S of x3 with 44 * |lines of S| < |S|
  have hne : (x3.powerset.filter (fun S => 44 * (S.biUnion x4).card < S.card)).Nonempty :=
    ⟨x3, by rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨subset_refl _, h⟩⟩
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image _ Finset.card hne
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hSsub, hSlt⟩ := hS
  have key : ∀ T ⊆ S, 44 * (T.biUnion x4).card < T.card → S.card ≤ T.card := by
    intro T hT hTlt
    exact hmin T (by rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hT.trans hSsub, hTlt⟩)
  refine ⟨S, hSsub, ?_, ?_⟩
  · have hSne : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp at hSlt
    obtain ⟨e, he⟩ := hSne
    by_contra hneq
    have hsub : S.erase e ⊆ S := Finset.erase_subset e S
    have hU : ((S.erase e).biUnion x4).card ≤ (S.biUnion x4).card :=
      Finset.card_le_card (Finset.biUnion_subset_biUnion_of_subset_left x4 hsub)
    have hcard : (S.erase e).card = S.card - 1 := Finset.card_erase_of_mem he
    have h2 := key (S.erase e) hsub (by omega)
    omega
  · intro l hl
    by_contra hlt
    have hlt' : (S.filter (fun x => l ∈ x4 x)).card < 45 := by
      exact not_le.mp hlt
    obtain ⟨T, hT⟩ : ∃ T, T = S.filter (fun x => l ∈ x4 x) := ⟨_, rfl⟩
    rw [← hT] at hlt'
    have hS' : S \ T ⊆ S := Finset.sdiff_subset
    have hTsub : T ⊆ S := by rw [hT]; exact Finset.filter_subset _ _
    have hcard : (S \ T).card = S.card - T.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hTsub]
    have hTpos : 0 < T.card := by
      rw [Finset.mem_biUnion] at hl
      obtain ⟨x, hx, hlx⟩ := hl
      exact Finset.card_pos.mpr ⟨x, by rw [hT, Finset.mem_filter]; exact ⟨hx, hlx⟩⟩
    have hTle : T.card ≤ S.card := Finset.card_le_card hTsub
    have hUsub : (S \ T).biUnion x4 ⊆ (S.biUnion x4).erase l := by
      intro y hy
      rw [Finset.mem_biUnion] at hy
      obtain ⟨x, hx, hyx⟩ := hy
      rw [Finset.mem_sdiff] at hx
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_biUnion.mpr ⟨x, hx.1, hyx⟩⟩
      rintro rfl
      exact hx.2 (by rw [hT, Finset.mem_filter]; exact ⟨hx.1, hyx⟩)
    have hU : ((S \ T).biUnion x4).card ≤ (S.biUnion x4).card - 1 := by
      have := Finset.card_le_card hUsub
      rw [Finset.card_erase_of_mem hl] at this
      exact this
    have hUpos : 0 < (S.biUnion x4).card := Finset.card_pos.mpr ⟨l, hl⟩
    have h1 : 44 * ((S \ T).biUnion x4).card ≤ 44 * ((S.biUnion x4).card - 1) :=
      Nat.mul_le_mul_left _ hU
    have h2 := key (S \ T) hS' (by omega)
    omega
