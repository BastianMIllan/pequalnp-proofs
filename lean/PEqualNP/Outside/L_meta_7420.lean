import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7420

theorem zero_ne_one' (n : ℕ) [NeZero n] : (0 : Fin (n + 1)) ≠ 1 := by
  intro h
  have h1 := congrArg Fin.val h
  have hn : n ≠ 0 := NeZero.ne n
  rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega)] at h1
  exact absurd h1 (by decide)

end PEqualNP.Outside.L_meta_7420

theorem PEqualNP.Outside.L_meta_7420 : ∀ (x1 : ℕ) [x2 : NeZero x1] (x3 : Fin (x1 + (1 : ℕ)) → Fin (x1 * x1) → Fin x1), (∀ (x4 x5 : Fin (x1 + (1 : ℕ))), x4 ≠ x5 → Function.Bijective fun (x7 : Fin (x1 * x1)) => (x3 x4 x7, x3 x5 x7)) → ∃ (x5 : Fin x1 × Fin x1 ≃ Fin (x1 * x1)) (x6 : Fin (x1 + (1 : ℕ)) → Fin x1 ≃ Fin x1), (∀ (x7 : Fin x1 × Fin x1), (x6 (0 : Fin (x1 + (1 : ℕ)))) (x3 (0 : Fin (x1 + (1 : ℕ))) (x5 x7)) = x7.1 ∧ (x6 (1 : Fin (x1 + (1 : ℕ)))) (x3 (1 : Fin (x1 + (1 : ℕ))) (x5 x7)) = x7.2) ∧ ∀ (x7 : Fin (x1 + (1 : ℕ))), x7 ≠ (0 : Fin (x1 + (1 : ℕ))) → ∀ (x9 : Fin x1), (x6 x7) (x3 x7 (x5 ((0 : Fin x1), x9))) = x9 := by
  intro n _ f hf
  have h01 : (0 : Fin (n + 1)) ≠ 1 := PEqualNP.Outside.L_meta_7420.zero_ne_one' n
  let F := Equiv.ofBijective _ (hf 0 1 h01)
  have hF : ∀ p : Fin n × Fin n, f 0 (F.symm p) = p.1 ∧ f 1 (F.symm p) = p.2 := by
    intro p
    have := F.apply_symm_apply p
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hinj : ∀ i : Fin (n + 1), i ≠ 0 →
      Function.Bijective (fun b : Fin n => f i (F.symm ((0 : Fin n), b))) := by
    intro i hi
    apply Finite.injective_iff_bijective.mp
    intro b b' hbb
    have hb := hf 0 i (Ne.symm hi)
    have h0 : f 0 (F.symm ((0 : Fin n), b)) = f 0 (F.symm ((0 : Fin n), b')) := by
      rw [(hF _).1, (hF _).1]
    have heq : F.symm ((0 : Fin n), b) = F.symm ((0 : Fin n), b') := by
      apply hb.1
      simp only [Prod.mk.injEq]
      exact ⟨h0, hbb⟩
    have := congrArg (fun x => f 1 x) heq
    simp only [(hF _).2] at this
    exact this
  classical
  refine ⟨F.symm, fun i => if hi : i = 0 then Equiv.refl _ else (Equiv.ofBijective _ (hinj i hi)).symm, ?_, ?_⟩
  · intro p
    refine ⟨?_, ?_⟩
    · beta_reduce
      rw [dif_pos rfl, Equiv.refl_apply]
      exact (hF p).1
    · beta_reduce
      rw [dif_neg (Ne.symm h01)]
      rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply, (hF _).2, (hF _).2]
  · intro i hi b
    beta_reduce
    rw [dif_neg hi]
    rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply]
