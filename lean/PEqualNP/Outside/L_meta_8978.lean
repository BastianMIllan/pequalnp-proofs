import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8978

theorem aux : ∀ (k n : ℕ), n < 2 ^ k →
    (Finset.univ.sum (fun i : Fin k => if n.testBit (i : ℕ) = true then 2 ^ (i : ℕ) else 0)) = n
  | 0, n, h => by
    simp at h
    subst h
    simp
  | k + 1, n, h => by
    rw [Fin.sum_univ_succ]
    have hlt : n / 2 < 2 ^ k := by
      rw [pow_succ] at h
      omega
    have ih := aux k (n / 2) hlt
    have hs : (Finset.univ.sum (fun i : Fin k =>
        if n.testBit ((Fin.succ i : Fin (k + 1)) : ℕ) = true then 2 ^ ((Fin.succ i : Fin (k + 1)) : ℕ) else 0))
        = 2 * (Finset.univ.sum (fun i : Fin k =>
          if (n / 2).testBit (i : ℕ) = true then 2 ^ (i : ℕ) else 0)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      simp only [Fin.val_succ, Nat.testBit_succ, pow_succ]
      split_ifs <;> ring
    rw [hs, ih]
    simp only [Fin.val_zero, pow_zero, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
    · simp [h2]
      omega
    · simp [h2]
      omega

end PEqualNP.Outside.L_meta_8978

theorem PEqualNP.Outside.L_meta_8978 : ∀ (k : ℕ) (u : Fin (2 ^ k)), PEqualNP.MetaComplexity.tableIndex (fun i : Fin k => (u : ℕ).testBit i) = (u : ℕ) := by
  intro k u
  unfold PEqualNP.MetaComplexity.tableIndex
  exact PEqualNP.Outside.L_meta_8978.aux k u u.isLt
