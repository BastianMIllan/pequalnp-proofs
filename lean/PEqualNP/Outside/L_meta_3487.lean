import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3487

theorem core {α β : Type} [DecidableEq α] [DecidableEq β] (S : Finset (α × β))
    (h : ∀ (p p' : α) (l l' : β), p ≠ p' → l ≠ l' → (p, l) ∈ S → (p', l) ∈ S →
      (p, l') ∈ S → (p', l') ∈ S → False)
    (ha : (S.image Prod.fst).card ≤ 7656) :
    S.card + 44 ≤ 44 * ((S.image Prod.fst).card + (S.image Prod.snd).card) ∨ S = ∅ := by
  classical
  set A := S.image Prod.fst with hA
  set B := S.image Prod.snd with hB
  let F : β → Finset α := fun r => (S.filter (fun e => e.2 = r)).image Prod.fst
  have hF : ∀ r, (S.filter (fun e => e.2 = r)).card = (F r).card := by
    intro r
    symm
    apply Finset.card_image_of_injOn
    intro e he e' he' hee
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at he he'
    exact Prod.ext hee (he.2.trans he'.2.symm)
  have hcard : S.card = ∑ r ∈ B, (F r).card := by
    rw [Finset.card_eq_sum_card_image Prod.snd S]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    exact hF r
  have hmemF : ∀ r p, p ∈ F r ↔ (p, r) ∈ S := by
    intro r p
    simp only [F, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨e, ⟨he, he2⟩, rfl⟩
      have : e = (e.1, r) := Prod.ext rfl he2
      rw [this] at he; exact he
    · intro hp; exact ⟨(p, r), ⟨hp, rfl⟩, rfl⟩
  have hdisj : ∀ r ∈ B, ∀ r' ∈ B, r ≠ r' → Disjoint (F r).offDiag (F r').offDiag := by
    intro r _ r' _ hrr
    rw [Finset.disjoint_left]
    rintro ⟨p, p'⟩ h1 h2
    rw [Finset.mem_offDiag] at h1 h2
    simp only [hmemF] at h1 h2
    exact h p p' r r' h1.2.2 hrr h1.1 h1.2.1 h2.1 h2.2.1
  have hsub : B.biUnion (fun r => (F r).offDiag) ⊆ A.offDiag := by
    intro q hq
    rw [Finset.mem_biUnion] at hq
    obtain ⟨r, _, hq⟩ := hq
    rw [Finset.mem_offDiag] at hq ⊢
    simp only [hmemF] at hq
    refine ⟨?_, ?_, hq.2.2⟩
    · rw [hA, Finset.mem_image]; exact ⟨_, hq.1, rfl⟩
    · rw [hA, Finset.mem_image]; exact ⟨_, hq.2.1, rfl⟩
  have hsum : ∑ r ∈ B, (F r).offDiag.card ≤ A.offDiag.card := by
    rw [← Finset.card_biUnion hdisj]
    exact Finset.card_le_card hsub
  have hpt : ∀ r ∈ B, 174 * (F r).card ≤ (F r).offDiag.card + 7656 := by
    intro r _
    rw [Finset.offDiag_card]
    have h1 := Nat.le_mul_self (F r).card
    have h2 : 175 * (F r).card ≤ (F r).card * (F r).card + 7656 := by
      rcases Nat.lt_or_ge (F r).card 88 with hd | hd
      · rcases Nat.lt_or_ge (F r).card 87 with hd' | hd'
        · nlinarith
        · have : (F r).card = 87 := by omega
          rw [this]
      · nlinarith
    omega
  have htot : 174 * S.card ≤ A.offDiag.card + 7656 * B.card := by
    rw [hcard, Finset.mul_sum]
    calc ∑ r ∈ B, 174 * (F r).card ≤ ∑ r ∈ B, ((F r).offDiag.card + 7656) :=
          Finset.sum_le_sum hpt
      _ = ∑ r ∈ B, (F r).offDiag.card + 7656 * B.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ A.offDiag.card + 7656 * B.card := by omega
  rw [Finset.offDiag_card] at htot
  have hA2 : A.card * A.card - A.card ≤ 7656 * (A.card - 1) := by
    rw [← Nat.mul_sub_one]
    exact Nat.mul_le_mul_right _ ha
  by_cases hS : S = ∅
  · exact Or.inr hS
  · left
    have hApos : 1 ≤ A.card := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      rw [Finset.card_eq_zero, hA, Finset.image_eq_empty] at h0
      exact hS h0
    omega

end PEqualNP.Outside.L_meta_3487

open PEqualNP.Outside.L_meta_3487 in
theorem PEqualNP.Outside.L_meta_3487 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)), (∀ (x3 x4 x5 x6 : Fin x1), x3 ≠ x4 → x5 ≠ x6 → ¬((x3, x5) ∈ x2 ∧ (x4, x5) ∈ x2 ∧ (x3, x6) ∈ x2 ∧ (x4, x6) ∈ x2)) → Min.min (Finset.image Prod.fst x2).card (Finset.image Prod.snd x2).card ≤ (7656 : ℕ) → x2.card ≤ (44 : ℕ) * ((Finset.image Prod.fst x2).card + (Finset.image Prod.snd x2).card - (1 : ℕ)) := by
  intro n S hS hmin
  rcases Nat.le_total (Finset.image Prod.fst S).card (Finset.image Prod.snd S).card with hle | hle
  · have ha : (S.image Prod.fst).card ≤ 7656 := by
      rw [Nat.min_eq_left hle] at hmin; exact hmin
    rcases core S (fun p p' l l' hp hl h1 h2 h3 h4 => hS p p' l l' hp hl ⟨h1, h2, h3, h4⟩) ha
      with h | h
    · omega
    · subst h; simp
  · have hb : (S.image Prod.snd).card ≤ 7656 := by
      rw [Nat.min_eq_right hle] at hmin; exact hmin
    set T := S.image Prod.swap with hT
    have hTf : T.image Prod.fst = S.image Prod.snd := by
      rw [hT, Finset.image_image]; rfl
    have hTs : T.image Prod.snd = S.image Prod.fst := by
      rw [hT, Finset.image_image]; rfl
    have hTc : T.card = S.card :=
      Finset.card_image_of_injective _ Prod.swap_injective
    have hmemT : ∀ (a b : Fin n), (a, b) ∈ T ↔ (b, a) ∈ S := by
      intro a b
      rw [hT, Finset.mem_image]
      constructor
      · rintro ⟨e, he, hee⟩
        have : e = (b, a) := by
          rw [← Prod.swap_swap e, hee]; rfl
        rw [this] at he; exact he
      · intro h; exact ⟨(b, a), h, rfl⟩
    have hc := core T (fun p p' l l' hp hl h1 h2 h3 h4 => by
        simp only [hmemT] at h1 h2 h3 h4
        exact hS l l' p p' hl hp ⟨h1, h3, h2, h4⟩) (by rw [hTf]; exact hb)
    rw [hTf, hTs, hTc] at hc
    rcases hc with h | h
    · omega
    · have : S = ∅ := by
        rw [← Finset.card_eq_zero, ← hTc, h]; rfl
      subst this; simp
