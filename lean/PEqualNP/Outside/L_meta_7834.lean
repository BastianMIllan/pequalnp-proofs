import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7834

theorem aux (n : ℕ) (d : Fin n → ℕ) (k : ℕ) : ∀ (T : Finset (Fin n)), T.card = k →
    ∀ (G : SimpleGraph (Fin n)), G.support ⊆ ↑T → ∃ H ≤ G,
      (∀ v, (H.neighborSet v).ncard = 0 ∨ d v < (H.neighborSet v).ncard) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard + ∑ v ∈ T, d v := by
  refine Nat.strong_induction_on k ?_
  intro k ih T hT G hG
  by_cases hall : ∀ v, (G.neighborSet v).ncard = 0 ∨ d v < (G.neighborSet v).ncard
  · exact ⟨G, le_rfl, hall, by omega⟩
  · push Not at hall
    obtain ⟨v, hv0, hvd⟩ := hall
    have hvS : v ∈ G.support := by
      rw [SimpleGraph.mem_support]
      by_contra h
      push Not at h
      apply hv0
      have he : G.neighborSet v = ∅ := by
        ext w
        simp [SimpleGraph.mem_neighborSet, h w]
      rw [he, Set.ncard_empty]
    have hvT : v ∈ T := hG hvS
    have hG'S : (G.deleteIncidenceSet v).support ⊆ ↑(T.erase v) := by
      intro w hw
      have hw' := G.support_deleteIncidenceSet_subset v hw
      rw [Set.mem_sdiff, Set.mem_singleton_iff] at hw'
      rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨hG hw'.1, hw'.2⟩
    have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨v, hvT⟩
    have hlt : (T.erase v).card < k := by
      rw [Finset.card_erase_of_mem hvT]; omega
    obtain ⟨H, hH, hdeg, hcount⟩ := ih (T.erase v).card hlt (T.erase v) rfl _ hG'S
    refine ⟨H, le_trans hH (G.deleteIncidenceSet_le v), hdeg, ?_⟩
    have hsum : ∑ w ∈ T, d w = d v + ∑ w ∈ T.erase v, d w := (Finset.add_sum_erase T d hvT).symm
    have hedge : G.edgeSet.ncard =
        (G.deleteIncidenceSet v).edgeSet.ncard + (G.neighborSet v).ncard := by
      have h1 : (G.deleteIncidenceSet v).edgeSet = G.edgeSet \ G.incidenceSet v :=
        G.edgeSet_deleteIncidenceSet v
      have h2 : (G.incidenceSet v).ncard = (G.neighborSet v).ncard := by
        rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
        exact Nat.card_congr (G.incidenceSetEquivNeighborSet v)
      rw [h1, ← h2]
      exact (Set.ncard_sdiff_add_ncard_of_subset (G.incidenceSet_subset v) (Set.toFinite _)).symm
    omega

end PEqualNP.Outside.L_meta_7834

theorem PEqualNP.Outside.L_meta_7834 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : Fin x1 → ℕ), x2.support ⊆ ↑x3 → ∃ x6 ≤ x2, (∀ (x7 : Fin x1), (x6.neighborSet x7).ncard = (0 : ℕ) ∨ x4 x7 < (x6.neighborSet x7).ncard) ∧ x2.edgeSet.ncard ≤ x6.edgeSet.ncard + ∑ x7 ∈ x3, x4 x7 := by
  intro n G T d hG
  exact PEqualNP.Outside.L_meta_7834.aux n d T.card T rfl G hG
