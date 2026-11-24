import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3565 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.FactorSubst.liveSize n C = C.size → ∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k := by
  intro n C h k hk
  have hsub : PEqualNP.FactorSubst.liveGates n C ⊆ Finset.range C.gates.length :=
    Finset.filter_subset _ _
  have hcard : (Finset.range C.gates.length).card ≤ (PEqualNP.FactorSubst.liveGates n C).card := by
    rw [Finset.card_range]
    unfold PEqualNP.FactorSubst.liveSize at h
    unfold PEqualNP.CircuitLowerBounds.Circuit.size at h
    omega
  have heq : PEqualNP.FactorSubst.liveGates n C = Finset.range C.gates.length :=
    Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : k ∈ PEqualNP.FactorSubst.liveGates n C := by
    rw [heq]
    exact Finset.mem_range.mpr hk
  unfold PEqualNP.FactorSubst.liveGates at hmem
  rw [Finset.mem_filter] at hmem
  obtain ⟨_, hn, h1 | h2⟩ := hmem
  · exact ⟨hk, Or.inl (by omega)⟩
  · exact ⟨hk, Or.inr ⟨hn, h2⟩⟩
