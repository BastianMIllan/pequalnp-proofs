import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7416

theorem ltpow (n : ℕ) : n < 2 ^ n := by
  first
  | exact Nat.lt_two_pow_self
  | exact Nat.lt_two_pow n
  | exact Nat.lt_pow_self (by norm_num)

theorem tbf (n i : ℕ) (h : n ≤ i) : n.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (ltpow n) (Nat.pow_le_pow_right (by norm_num) h))

theorem memle (l : List ℕ) (a : ℕ) (h : a ∈ l) : a ≤ l.sum := by
  first
  | exact List.le_sum_of_mem h
  | exact List.single_le_sum (fun _ _ => Nat.zero_le _) a h

end PEqualNP.Outside.L_meta_7416

open PEqualNP.Outside.L_meta_7416 in
theorem PEqualNP.Outside.L_meta_7416 : ∀ (x1 : List ℕ) (x2 : ℕ), ∃ (x3 : ℕ), (∀ (x4 : ℕ), ∃ (x5 : ℕ), x3.testBit x5 = Bool.true ∧ x2.testBit x5 = x2.testBit x4 ∧ ∀ x6 ∈ x1, x6.testBit x5 = x6.testBit x4) ∧ (∀ x4 ∈ x1, x4 &&& x3 = x4) ∧ x2 &&& x3 = x2 := by
  intro x1 x2
  have hx2 : x2 ≤ x2 + x1.sum := Nat.le_add_right _ _
  have hx1 : ∀ x6 ∈ x1, x6 ≤ x2 + x1.sum := fun x6 h => le_trans (memle x1 x6 h) (Nat.le_add_left _ _)
  refine ⟨2 ^ (x2 + x1.sum + 1) - 1, fun x4 => ?_, fun x4 hx4 => ?_, ?_⟩
  · by_cases h : x4 ≤ x2 + x1.sum
    · refine ⟨x4, ?_, rfl, fun _ _ => rfl⟩
      rw [Nat.testBit_two_pow_sub_one]
      simp only [decide_eq_true_eq]
      omega
    · refine ⟨x2 + x1.sum, ?_, ?_, ?_⟩
      · rw [Nat.testBit_two_pow_sub_one]
        simp
      · rw [tbf x2 _ hx2, tbf x2 x4 (by omega)]
      · intro x6 hx6
        have := hx1 x6 hx6
        rw [tbf x6 _ this, tbf x6 x4 (by omega)]
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    by_cases h : i < x2 + x1.sum + 1
    · simp [h]
    · have := hx1 x4 hx4
      rw [tbf x4 i (by omega)]
      simp
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    by_cases h : i < x2 + x1.sum + 1
    · simp [h]
    · rw [tbf x2 i (by omega)]
      simp
