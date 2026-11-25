import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8561

def f {α : Type*} [DecidableEq α] (l : List α) (k i : ℕ) : Finset α :=
  if 2 * k - 2 < i then ∅
  else if i % 2 = 0 then (l.take (i / 2 + 1)).toFinset
  else ((l.drop (i / 2 + 1)).take 1).toFinset

theorem f_even {α : Type*} [DecidableEq α] (l : List α) (k i : ℕ) (hi : i ≤ 2 * k - 2)
    (he : i % 2 = 0) : f l k i = (l.take (i / 2 + 1)).toFinset := by
  unfold f
  rw [if_neg (show ¬ (2 * k - 2 < i) by omega), if_pos he]

theorem f_odd {α : Type*} [DecidableEq α] (l : List α) (k i : ℕ) (hi : i ≤ 2 * k - 2)
    (he : i % 2 = 1) : f l k i = ((l.drop (i / 2 + 1)).take 1).toFinset := by
  unfold f
  rw [if_neg (show ¬ (2 * k - 2 < i) by omega), if_neg (show ¬ (i % 2 = 0) by omega)]

theorem f_big {α : Type*} [DecidableEq α] (l : List α) (k i : ℕ) (hi : 2 * k - 2 < i) :
    f l k i = ∅ := by
  unfold f
  rw [if_pos hi]

theorem card_take_one {α : Type*} [DecidableEq α] (l : List α) :
    (l.take 1).toFinset.card ≤ 1 := by
  refine (List.toFinset_card_le _).trans ?_
  rw [List.length_take]
  omega

end PEqualNP.Outside.L_meta_8561

theorem PEqualNP.Outside.L_meta_8561 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)), x3.Nonempty → ∃ (x5 : Finset ℕ) (x6 : ℕ → Finset (Fin x1 × Fin x2)), x5 ⊆ Finset.range ((2 : ℕ) * x3.card - (1 : ℕ)) ∧ x6 ((2 : ℕ) * x3.card - (2 : ℕ)) = x3 ∧ x5.card + (1 : ℕ) = x3.card ∧ (∀ x7 ∉ x5, (x6 x7).card ≤ (1 : ℕ)) ∧ ∀ x7 ∈ x5, (2 : ℕ) ≤ x7 ∧ x6 x7 = x6 (x7 - (2 : ℕ)) ∪ x6 (x7 - (1 : ℕ)) := by
  intro x1 x2 S hS
  classical
  have hk1 : 1 ≤ S.card := Finset.card_pos.mpr hS
  have hlen : S.toList.length = S.card := Finset.length_toList S
  refine ⟨(Finset.range (S.card - 1)).image (fun j => 2 * j + 2),
    PEqualNP.Outside.L_meta_8561.f S.toList S.card, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_image, Finset.mem_range] at hi ⊢
    obtain ⟨j, hj, rfl⟩ := hi
    omega
  · rw [PEqualNP.Outside.L_meta_8561.f_even _ _ _ (le_refl _) (by omega)]
    have : (2 * S.card - 2) / 2 + 1 = S.toList.length := by rw [hlen]; omega
    rw [this, List.take_length, Finset.toList_toFinset]
  · rw [Finset.card_image_of_injective _ (by
      intro a b h
      have h' : 2 * a + 2 = 2 * b + 2 := h
      omega), Finset.card_range]
    omega
  · intro i hi
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and] at hi
    by_cases h1 : 2 * S.card - 2 < i
    · rw [PEqualNP.Outside.L_meta_8561.f_big _ _ _ h1]
      simp
    · by_cases h2 : i % 2 = 0
      · have h0 : i = 0 := by
          by_contra hne
          exact hi (i / 2 - 1) (by omega) (by omega)
        subst h0
        rw [PEqualNP.Outside.L_meta_8561.f_even _ _ _ (by omega) h2]
        exact PEqualNP.Outside.L_meta_8561.card_take_one _
      · rw [PEqualNP.Outside.L_meta_8561.f_odd _ _ _ (by omega) (by omega)]
        exact PEqualNP.Outside.L_meta_8561.card_take_one _
  · intro i hi
    simp only [Finset.mem_image, Finset.mem_range] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    refine ⟨by omega, ?_⟩
    rw [PEqualNP.Outside.L_meta_8561.f_even _ _ (2 * j + 2) (by omega) (by omega),
      PEqualNP.Outside.L_meta_8561.f_even _ _ (2 * j + 2 - 2) (by omega) (by omega),
      PEqualNP.Outside.L_meta_8561.f_odd _ _ (2 * j + 2 - 1) (by omega) (by omega)]
    have e1 : (2 * j + 2) / 2 + 1 = (j + 1) + 1 := by omega
    have e2 : (2 * j + 2 - 2) / 2 + 1 = j + 1 := by omega
    have e3 : (2 * j + 2 - 1) / 2 + 1 = j + 1 := by omega
    rw [e1, e2, e3, List.take_add, List.toFinset_append]
