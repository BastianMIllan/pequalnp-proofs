import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6510

open Finset

variable {m n : ℕ}

def nb (E : Finset (Fin m × Fin n)) (a : Fin m) : Finset (Fin n) :=
  (E.filter (fun e => e.1 = a)).image Prod.snd

theorem mem_nb {E : Finset (Fin m × Fin n)} {a : Fin m} {b : Fin n} :
    b ∈ nb E a ↔ (a, b) ∈ E := by
  unfold nb
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨e, ⟨he, h1⟩, h2⟩
    subst h1
    subst h2
    exact he
  · intro h
    exact ⟨(a, b), ⟨h, rfl⟩, rfl⟩

def gap (E : Finset (Fin m × Fin n)) (A : Finset (Fin m)) : ℤ :=
  (A.card : ℤ) - ((A.biUnion (nb E)).card : ℤ)

theorem main (E : Finset (Fin m × Fin n)) :
    ∃ (M : Finset (Fin m × Fin n)) (P : Finset (Fin m)) (Q : Finset (Fin n)), M ⊆ E ∧
      (∀ x ∈ M, ∀ y ∈ M, x.1 = y.1 → x = y) ∧ (∀ x ∈ M, ∀ y ∈ M, x.2 = y.2 → x = y) ∧
      (∀ x ∈ E, x.1 ∈ P ∨ x.2 ∈ Q) ∧ P.card + Q.card ≤ M.card := by
  classical
  obtain ⟨A0, -, hA0⟩ :=
    Finset.exists_max_image (univ : Finset (Finset (Fin m))) (gap E) ⟨∅, mem_univ _⟩
  have hmax : ∀ s, gap E s ≤ gap E A0 := fun s => hA0 s (mem_univ _)
  have h0 : gap E ∅ = 0 := by simp [gap]
  have hd0 : 0 ≤ gap E A0 := h0 ▸ hmax ∅
  obtain ⟨d, hdg⟩ : ∃ d : ℕ, (d : ℤ) = gap E A0 := ⟨(gap E A0).toNat, Int.toNat_of_nonneg hd0⟩
  let t : Fin m → Finset (Fin n ⊕ Fin d) := fun a =>
    (nb E a).map Function.Embedding.inl ∪ (univ : Finset (Fin d)).map Function.Embedding.inr
  have hall : ∀ s : Finset (Fin m), s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · have hsub : (s.biUnion (nb E)).map Function.Embedding.inl ∪
          (univ : Finset (Fin d)).map Function.Embedding.inr ⊆ s.biUnion t := by
        intro z hz
        rw [mem_biUnion]
        rcases mem_union.mp hz with hz | hz
        · rw [mem_map] at hz
          obtain ⟨b, hb, rfl⟩ := hz
          rw [mem_biUnion] at hb
          obtain ⟨a, ha, hb⟩ := hb
          exact ⟨a, ha, mem_union_left _ (mem_map_of_mem _ hb)⟩
        · obtain ⟨a, ha⟩ := hne
          exact ⟨a, ha, mem_union_right _ hz⟩
      have hdisj : Disjoint ((s.biUnion (nb E)).map Function.Embedding.inl)
          ((univ : Finset (Fin d)).map (Function.Embedding.inr : Fin d ↪ Fin n ⊕ Fin d)) := by
        rw [disjoint_left]
        intro z h1 h2
        rw [mem_map] at h1 h2
        obtain ⟨b, -, rfl⟩ := h1
        obtain ⟨c, -, hc⟩ := h2
        simp at hc
      have hc := card_le_card hsub
      rw [card_union_of_disjoint hdisj, card_map, card_map, card_univ, Fintype.card_fin] at hc
      have hs := hmax s
      have e : gap E s = (s.card : ℤ) - ((s.biUnion (nb E)).card : ℤ) := rfl
      omega
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  let M : Finset (Fin m × Fin n) := E.filter (fun e => f e.1 = Sum.inl e.2)
  refine ⟨M, A0ᶜ, A0.biUnion (nb E), filter_subset _ _, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy h
    simp only [M, mem_filter] at hx hy
    have h2 : (Sum.inl x.2 : Fin n ⊕ Fin d) = Sum.inl y.2 := by rw [← hx.2, ← hy.2, h]
    exact Prod.ext h (Sum.inl_injective h2)
  · intro x hx y hy h
    simp only [M, mem_filter] at hx hy
    have h1 : f x.1 = f y.1 := by rw [hx.2, hy.2, h]
    exact Prod.ext (hfinj h1) h
  · intro x hx
    by_cases h : x.1 ∈ A0
    · right
      rw [mem_biUnion]
      exact ⟨x.1, h, mem_nb.mpr hx⟩
    · left
      exact mem_compl.mpr h
  · have hR : (univ.filter (fun a => ¬ ∃ b, f a = Sum.inl b)).card ≤ d := by
      have hsub : (univ.filter (fun a => ¬ ∃ b, f a = Sum.inl b)).image f ⊆
          (univ : Finset (Fin d)).map Function.Embedding.inr := by
        intro z hz
        rw [mem_image] at hz
        obtain ⟨a, ha, rfl⟩ := hz
        rw [mem_filter] at ha
        cases hfa : f a with
        | inl b => exact absurd ⟨b, hfa⟩ ha.2
        | inr c => exact mem_map.mpr ⟨c, mem_univ c, rfl⟩
      have := card_le_card hsub
      rwa [card_image_of_injective _ hfinj, card_map, card_univ, Fintype.card_fin] at this
    have hL : (univ.filter (fun a => ∃ b, f a = Sum.inl b)).card ≤ M.card := by
      have hsub : univ.filter (fun a => ∃ b, f a = Sum.inl b) ⊆ M.image Prod.fst := by
        intro a ha
        rw [mem_filter] at ha
        obtain ⟨b, hb⟩ := ha.2
        rw [mem_image]
        refine ⟨(a, b), ?_, rfl⟩
        simp only [M, mem_filter]
        refine ⟨?_, hb⟩
        have hm : (Sum.inl b : Fin n ⊕ Fin d) ∈ t a := hb ▸ hft a
        rcases mem_union.mp hm with h | h
        · obtain ⟨b', hb', e⟩ := mem_map.mp h
          have e' : b' = b := Sum.inl_injective e
          subst e'
          exact mem_nb.mp hb'
        · obtain ⟨c, -, e⟩ := mem_map.mp h
          simp at e
      exact (card_le_card hsub).trans card_image_le
    have htot := card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
      (fun a => ∃ b, f a = Sum.inl b)
    rw [card_univ, Fintype.card_fin] at htot
    have hcomp : (A0ᶜ).card = m - A0.card := by
      rw [card_compl, Fintype.card_fin]
    have hA0m : A0.card ≤ m := by
      have := card_le_univ A0
      rwa [Fintype.card_fin] at this
    have e : gap E A0 = (A0.card : ℤ) - ((A0.biUnion (nb E)).card : ℤ) := rfl
    omega

end PEqualNP.Outside.L_meta_6510

theorem PEqualNP.Outside.L_meta_6510 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)), ∃ (x4 : Finset (Fin x1 × Fin x2)) (x5 : Finset (Fin x1)) (x6 : Finset (Fin x2)), x4 ⊆ x3 ∧ (∀ x7 ∈ x4, ∀ x9 ∈ x4, x7.1 = x9.1 → x7 = x9) ∧ (∀ x7 ∈ x4, ∀ x9 ∈ x4, x7.2 = x9.2 → x7 = x9) ∧ (∀ x7 ∈ x3, x7.1 ∈ x5 ∨ x7.2 ∈ x6) ∧ x5.card + x6.card ≤ x4.card := by
  intro x1 x2 x3
  exact PEqualNP.Outside.L_meta_6510.main x3
