import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3454

theorem gate_mem (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ) (hg : g < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C g ∈ C.gates := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hg]
  exact List.getElem_mem hg

theorem three_le (R F : Finset ℕ) (n : ℕ) :
    (R.filter (fun w => w < n)).card + (R.filter (fun w => n ≤ w ∧ w - n ∉ F)).card
      + (R.filter (fun w => n ≤ w ∧ w - n ∈ F)).card ≤ R.card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc _ ≤ ∑ _w ∈ R, 1 := by
        apply Finset.sum_le_sum
        intro w _
        by_cases h1 : w < n
        · have h2 : ¬ n ≤ w := by omega
          simp [h1, h2]
        · by_cases h2 : w - n ∈ F
          · have h3 : n ≤ w := by omega
            simp [h1, h2, h3]
          · have h3 : n ≤ w := by omega
            simp [h1, h2, h3]
    _ = R.card := by simp

end PEqualNP.Outside.L_meta_3454

theorem PEqualNP.Outside.L_meta_3454 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ g ∈ F, g < C.gates.length) → ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => w < n)).card + ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter (fun w => n ≤ w ∧ w - n ∉ F)).card + (F.filter (fun g => n + g ∈ F.biUnion (fun g' => (PEqualNP.MetaComplexity.NestedCover.gateAt C g').inputs.toFinset))).card ≤ 2 * F.card := by
  intro n C F hC hF
  set R := F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset) with hR
  have h3 : (F.filter (fun g => n + g ∈ R)).card ≤ (R.filter (fun w => n ≤ w ∧ w - n ∈ F)).card := by
    apply Finset.card_le_card_of_injOn (fun g => n + g)
    · intro g hg
      rw [Finset.mem_coe, Finset.mem_filter] at hg
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨hg.2, Nat.le_add_right n g, ?_⟩
      simpa using hg.1
    · intro a _ b _ hab
      simp only at hab
      omega
  have hRc : R.card ≤ 2 * F.card := by
    calc R.card ≤ ∑ g ∈ F, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _g ∈ F, 2 := by
          apply Finset.sum_le_sum
          intro g hg
          have hm := PEqualNP.Outside.L_meta_3454.gate_mem C g (hF g hg)
          have hl := hC.2.2 _ hm
          calc _ ≤ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.length := List.toFinset_card_le _
            _ = 2 := hl
      _ = 2 * F.card := by simp [mul_comm]
  have h4 := PEqualNP.Outside.L_meta_3454.three_le R F n
  omega
