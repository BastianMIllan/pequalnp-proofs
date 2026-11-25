import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6654

-- Every point of a projective plane of order q lies on exactly q + 1 lines.
theorem lines_through {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] (hq : 0 < q)
    (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  classical
  haveI : Nonempty (Fin N) := ⟨p⟩
  have hex : ∀ p' : Fin N, p' ≠ p → ∃ l, I p l ∧ I p' l :=
    fun p' h => (hU p p' (Ne.symm h)).exists
  choose! g hg using hex
  have h1 := Finset.card_eq_sum_card_fiberwise (f := g) (s := Finset.univ.filter (fun p' => p' ≠ p))
    (t := Finset.univ.filter (fun l => I p l)) (by
      intro p' hp'
      simp only [Finset.mem_coe, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq] at hp' ⊢
      exact (hg p' hp').1)
  have h2 : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.filter (fun p' => p' ≠ p)).filter (fun p' => g p' = l)).card = q := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    have : (Finset.univ.filter (fun p' => p' ≠ p)).filter (fun p' => g p' = l) =
        (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · rintro ⟨hne, rfl⟩
        exact ⟨hne, (hg p' hne).2⟩
      · rintro ⟨hne, hp'⟩
        exact ⟨hne, (hU p p' (Ne.symm hne)).unique (hg p' hne) ⟨hl, hp'⟩⟩
    rw [this, Finset.card_erase_of_mem (by simp [hl]), ← Fintype.card_subtype, hL]
    simp
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h1
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [← h1, hN, Nat.add_sub_cancel]
  ring

theorem dual {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] (hq : 0 < q)
    (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) (l l' : Fin N)
    (hne : l ≠ l') : ∃! p : Fin N, I p l ∧ I p l' := by
  classical
  have uniq : ∀ {p p' l l' : Fin N}, p ≠ p' → I p l → I p' l → I p l' → I p' l' → l = l' :=
    fun hp h1 h2 h3 h4 => (hU _ _ hp).unique ⟨h1, h2⟩ ⟨h3, h4⟩
  have hne' : ∀ {p p' : Fin N}, I p l → I p l' → I p' l → I p' l' → p = p' := by
    intro p p' h1 h2 h3 h4
    by_contra h
    exact hne (uniq h h1 h3 h2 h4)
  suffices hex : ∃ p, I p l ∧ I p l' by
    obtain ⟨p, hp⟩ := hex
    exact ⟨p, hp, fun p' hp' => hne' hp'.1 hp'.2 hp.1 hp.2⟩
  have hpos : 0 < Fintype.card {p // I p l} := by rw [hL]; omega
  obtain ⟨⟨p, hp⟩⟩ := Fintype.card_pos_iff.mp hpos
  by_cases hp' : I p l'
  · exact ⟨p, hp, hp'⟩
  have hx : ∀ x : Fin N, I x l' → x ≠ p := fun x hxl h => hp' (h ▸ hxl)
  have hm : ∀ x : Fin N, I x l' → ∃ m, I p m ∧ I x m :=
    fun x hxl => (hU p x (hx x hxl).symm).exists
  choose! f hf using hm
  set S := Finset.univ.filter (fun x => I x l') with hS
  have hSc : S.card = q + 1 := by rw [hS, ← Fintype.card_subtype, hL]
  have hinj : Set.InjOn f S := by
    intro x hxS y hyS hxy
    simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hxS hyS
    by_contra h
    have h2 : I y (f x) := by rw [hxy]; exact (hf y hyS).2
    have h3 : f x = l' := uniq h (hf x hxS).2 h2 hxS hyS
    exact hp' (h3 ▸ (hf x hxS).1)
  have himg : S.image f ⊆ Finset.univ.filter (fun m => I p m) := by
    intro m hm
    simp only [Finset.mem_image, hS, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    obtain ⟨x, hxS, rfl⟩ := hm
    exact (hf x hxS).1
  have hcard : (Finset.univ.filter (fun m => I p m)).card ≤ (S.image f).card := by
    rw [Finset.card_image_of_injOn hinj, hSc, lines_through hq hN hL hU p]
  have heq := Finset.eq_of_subset_of_card_le himg hcard
  have hl : l ∈ S.image f := by rw [heq]; simp [hp]
  simp only [Finset.mem_image, hS, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  obtain ⟨x, hxS, hfx⟩ := hl
  refine ⟨x, ?_, hxS⟩
  rw [← hfx]
  exact (hf x hxS).2

end PEqualNP.Outside.L_meta_6654

theorem PEqualNP.Outside.L_meta_6654 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (131 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x9 x10 } = x1 + (1 : ℕ)) ∧ ∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x12 x9 ∧ x3 x12 x10 := by
  intro q N I _ hq hN hL hU
  refine ⟨fun p => ?_, fun l l' h => PEqualNP.Outside.L_meta_6654.dual (by omega) hN hL hU l l' h⟩
  rw [Fintype.card_subtype]
  exact PEqualNP.Outside.L_meta_6654.lines_through (by omega) hN hL hU p
