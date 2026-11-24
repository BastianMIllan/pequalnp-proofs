import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_327 : ∀ {n m : ℕ} (S : Fin m → Finset (Fin n)) (k : ℕ) (C : PEqualNP.PointTypes.IFun n m), (∀ (p : Fin n) (T : Finset (Fin m)), PEqualNP.PointTypes.IsOnePointNeg S k p T → C {p} T = false) → 0 < n → PEqualNP.PointTypes.numTypes S k (fun _ : Fin 1 => C) = 1 := by
  intro n m S k C hC hn
  have h : ∀ p : Fin n, PEqualNP.PointTypes.ptype S k (fun _ : Fin 1 => C) p = Finset.univ := by
    intro p
    apply Finset.eq_univ_of_forall
    intro j
    have hneg : PEqualNP.PointTypes.IsOnePointNeg S k p ∅ :=
      ⟨by simp, fun l hl => by simp at hl⟩
    unfold PEqualNP.PointTypes.ptype
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ∅, hneg, hC p ∅ hneg⟩
  unfold PEqualNP.PointTypes.numTypes
  have hfun : PEqualNP.PointTypes.ptype S k (fun _ : Fin 1 => C) = fun _ => Finset.univ := funext h
  rw [hfun, Finset.image_const ⟨⟨0, hn⟩, Finset.mem_univ _⟩, Finset.card_singleton]
