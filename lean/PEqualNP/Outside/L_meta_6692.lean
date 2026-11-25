import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6692

theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 0 < q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

theorem line_eq {N : ℕ} {S : Fin N → Finset (Fin N)}
    (huniq : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, a ∈ S l ∧ b ∈ S l)
    {a b : Fin N} (hab : a ≠ b) {l l' : Fin N} (h1 : a ∈ S l) (h2 : b ∈ S l)
    (h3 : a ∈ S l') (h4 : b ∈ S l') : l = l' :=
  (huniq a b hab).unique ⟨h1, h2⟩ ⟨h3, h4⟩

theorem pt_deg {q N : ℕ} {S : Fin N → Finset (Fin N)} (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, (S l).card = q + 1)
    (huniq : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, a ∈ S l ∧ b ∈ S l) (p : Fin N) :
    (Finset.univ.filter (fun l => p ∈ S l)).card = q + 1 := by
  let I (p l : Fin N) : Prop := p ∈ S l
  have hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1 := by
    intro l
    have e : Finset.univ.filter (fun p => I p l) = S l := by
      ext x
      simp [I]
    rw [e, hcard l]
  exact lines_through q N I hq hN hl huniq p

theorem meet {q N : ℕ} {S : Fin N → Finset (Fin N)} (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, (S l).card = q + 1)
    (huniq : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, a ∈ S l ∧ b ∈ S l) (l l' : Fin N) :
    ∃ x, x ∈ S l ∧ x ∈ S l' := by
  have hpos : 0 < (S l').card := by rw [hcard l']; omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  by_cases hpl : p ∈ S l
  · exact ⟨p, hpl, hp⟩
  have hne : ∀ a ∈ S l, a ≠ p := fun a ha e => hpl (e ▸ ha)
  choose! f hf using fun (a : Fin N) (h : a ≠ p) => (huniq a p h).exists
  have hinj : Set.InjOn f (S l : Set (Fin N)) := by
    intro a ha b hb hab
    by_contra hab'
    have ha' : a ∈ S l := ha
    have hb' : b ∈ S l := hb
    have e : f a = l :=
      line_eq huniq hab' (hf a (hne a ha')).1 (hab ▸ (hf b (hne b hb')).1) ha' hb'
    exact hpl (e ▸ (hf a (hne a ha')).2)
  have himg : (S l).image f ⊆ Finset.univ.filter (fun m => p ∈ S m) := by
    intro m hm
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf a (hne a ha)).2⟩
  have hc : ((S l).image f).card = q + 1 := by
    rw [Finset.card_image_of_injOn hinj, hcard]
  have heq := Finset.eq_of_subset_of_card_le himg (by rw [pt_deg hq hN hcard huniq p, hc])
  have hl' : l' ∈ (S l).image f := by
    rw [heq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
  obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp hl'
  exact ⟨a, ha, hfa ▸ (hf a (hne a ha)).1⟩

theorem avoid {q N : ℕ} {S : Fin N → Finset (Fin N)} (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, (S l).card = q + 1)
    (huniq : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, a ∈ S l ∧ b ∈ S l)
    (L : Finset (Fin N)) (hL : L.card ≤ q) :
    q ≤ (Finset.univ.filter (fun p => ∀ m ∈ L, p ∉ S m)).card := by
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) (fun p => ∀ m ∈ L, p ∉ S m)
  rw [Finset.card_univ, Fintype.card_fin] at h1
  rcases L.eq_empty_or_nonempty with hE | ⟨l0, hl0⟩
  · subst hE
    have e : (Finset.univ.filter (fun p : Fin N => ∀ m ∈ (∅ : Finset (Fin N)), p ∉ S m))
        = Finset.univ := by
      ext x
      simp
    rw [e, Finset.card_univ, Fintype.card_fin, hN]
    nlinarith
  · have h2 : Finset.univ.filter (fun p => ¬ ∀ m ∈ L, p ∉ S m) ⊆
        S l0 ∪ (L.erase l0).biUnion (fun m => S m \ S l0) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hp
      obtain ⟨m, hm, hpm⟩ := hp
      by_cases h : p ∈ S l0
      · exact Finset.mem_union_left _ h
      · apply Finset.mem_union_right
        rw [Finset.mem_biUnion]
        refine ⟨m, ?_, ?_⟩
        · rw [Finset.mem_erase]
          exact ⟨fun e => h (e ▸ hpm), hm⟩
        · exact Finset.mem_sdiff.mpr ⟨hpm, h⟩
    have h3 : ∀ m ∈ L.erase l0, (S m \ S l0).card ≤ q := by
      intro m _
      obtain ⟨x, hx1, hx2⟩ := meet hq hN hcard huniq m l0
      have hs : S m \ S l0 ⊆ (S m).erase x := by
        intro y hy
        rw [Finset.mem_sdiff] at hy
        rw [Finset.mem_erase]
        exact ⟨fun e => hy.2 (e ▸ hx2), hy.1⟩
      have := Finset.card_le_card hs
      rw [Finset.card_erase_of_mem hx1, hcard m] at this
      omega
    have h4 := Finset.card_le_card h2
    have h5 := Finset.card_union_le (S l0) ((L.erase l0).biUnion (fun m => S m \ S l0))
    have h6 := Finset.card_biUnion_le (s := L.erase l0) (t := fun m => S m \ S l0)
    have h7 : ∑ m ∈ L.erase l0, (S m \ S l0).card ≤ ∑ _m ∈ L.erase l0, q :=
      Finset.sum_le_sum h3
    rw [Finset.sum_const, smul_eq_mul] at h7
    have h8 := Finset.card_erase_add_one hl0
    rw [hcard l0] at h5
    have h9 : ((L.erase l0).card + 1) * q ≤ q * q := Nat.mul_le_mul_right q (by omega)
    have hN2 := hN
    nlinarith

end PEqualNP.Outside.L_meta_6692

theorem PEqualNP.Outside.L_meta_6692 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)),   (0 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x6 : Fin x2), (x3 x6).card = x1 + (1 : ℕ)) →         (∀ (x7 x8 : Fin x2), x7 ≠ x8 → ∃! x10 : Fin x2, x7 ∈ x3 x10 ∧ x8 ∈ x3 x10) →           (∀ (x8 : Fin x2),               have x9 : Finset (Fin x2) := {x9 : Fin x2 | x8 ∈ x3 x9};               x9.card = x1 + (1 : ℕ)) ∧             (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x11 ∈ x3 x8 ∧ x11 ∈ x3 x9) ∧               ∀ (x8 : Finset (Fin x2)),                 x8.card ≤ x1 →                   have x10 : Finset (Fin x2) := {x10 : Fin x2 | ∀ x11 ∈ x8, x10 ∉ x3 x11};                   x1 ≤ x10.card := by
  intro q N S hq hN hcard huniq
  refine ⟨fun p => ?_, fun l l' hne => ?_, fun L hL => ?_⟩
  · exact PEqualNP.Outside.L_meta_6692.pt_deg hq hN hcard huniq p
  · obtain ⟨x, hx1, hx2⟩ := PEqualNP.Outside.L_meta_6692.meet hq hN hcard huniq l l'
    refine ⟨x, ⟨hx1, hx2⟩, ?_⟩
    rintro y ⟨hy1, hy2⟩
    by_contra hxy
    exact hne (PEqualNP.Outside.L_meta_6692.line_eq huniq hxy hy1 hx1 hy2 hx2)
  · exact PEqualNP.Outside.L_meta_6692.avoid hq hN hcard huniq L hL
