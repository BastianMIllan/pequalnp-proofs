import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1719

-- two distinct lines share at most one point
lemma meet_le_one (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hu : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l) (m l : Fin N) (hne : m ≠ l) :
    (Finset.univ.filter (fun u => I u m ∧ I u l)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_contra hab
  obtain ⟨k, _, hk⟩ := hu a b hab
  exact hne ((hk m ⟨ha.1, hb.1⟩).trans (hk l ⟨ha.2, hb.2⟩).symm)

-- a point lies on at most q + 1 lines
lemma deg_le (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card ≤ q + 1 := by
  have hdisj : ∀ l ∈ Finset.univ.filter (fun l => I p l), ∀ l' ∈ Finset.univ.filter (fun l => I p l),
      l ≠ l' → Disjoint ((Finset.univ.filter (fun x => I x l)).erase p)
        ((Finset.univ.filter (fun x => I x l')).erase p) := by
    intro l hl1 l' hl2 hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx' hl1 hl2
    obtain ⟨m, _, hm⟩ := hu x p hx.1
    exact hne ((hm l ⟨hx.2, hl1⟩).trans (hm l' ⟨hx'.2, hl2⟩).symm)
  have hcard : ((Finset.univ.filter (fun l => I p l)).biUnion
      (fun l => (Finset.univ.filter (fun x => I x l)).erase p)).card
      = (Finset.univ.filter (fun l => I p l)).card * q := by
    rw [Finset.card_biUnion (by
      intro l hl1 l' hl2 hne
      exact hdisj l hl1 l' hl2 hne)]
    apply Finset.sum_const_nat
    intro l hl1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl1
    rw [Finset.card_erase_of_mem (by simp [hl1]), hl l]
    simp
  have hsub : ((Finset.univ.filter (fun l => I p l)).biUnion
      (fun l => (Finset.univ.filter (fun x => I x l)).erase p)) ⊆ Finset.univ.erase p := by
    intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_erase] at hx
    obtain ⟨l, _, hx1, _⟩ := hx
    simp [hx1]
  have h3 := Finset.card_le_card hsub
  rw [hcard, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin] at h3
  have h4 : (Finset.univ.filter (fun l => I p l)).card * q ≤ (q + 1) * q := by
    have h5 : N - 1 = (q + 1) * q := by
      rw [hN, Nat.add_sub_cancel]
      ring
    rw [h5] at h3
    exact h3
  exact Nat.le_of_mul_le_mul_right h4 (by omega)

end PEqualNP.Outside.L_meta_1719

theorem PEqualNP.Outside.L_meta_1719 : ∀ (q131 N131 r131 : ℕ) (I131 : Fin N131 → Fin N131 → Prop) [DecidableRel I131] (S131 W131 : Finset (Fin N131)), 2 ≤ q131 → N131 = q131 ^ 2 + q131 + 1 → (∀ l131f : Fin N131, (Finset.univ.filter (fun p131b => I131 p131b l131f)).card = q131 + 1) → (∀ pa131 pb131 : Fin N131, pa131 ≠ pb131 → ∃! lb131 : Fin N131, I131 pa131 lb131 ∧ I131 pb131 lb131) → (∀ (pz131 : Fin N131) (T131 : Finset (Fin N131)), T131.card ≤ r131 → (W131 \ W131.filter (fun l131 => ¬ I131 pz131 l131 ∧ l131 ∉ T131)).card ≤ q131 + 1 + r131 ∧ ∀ l131b ∈ W131.filter (fun l131a => ¬ I131 pz131 l131a ∧ l131a ∉ T131), (S131.filter (fun u131 => I131 u131 l131b)).card ≤ ((S131.filter (fun u131a => u131a ≠ pz131 ∧ ∀ m131 ∈ T131, ¬ I131 u131a m131)).filter (fun u131b => I131 u131b l131b)).card + r131) ∧ (∀ (wz131 : Fin N131) (Q131 : Finset (Fin N131)), Q131.card ≤ r131 → (W131 \ W131.filter (fun l131c => l131c ≠ wz131 ∧ ∀ p131 ∈ Q131, ¬ I131 p131 l131c)).card ≤ 1 + r131 * (q131 + 1) ∧ ∀ l131e ∈ W131.filter (fun l131d => l131d ≠ wz131 ∧ ∀ p131a ∈ Q131, ¬ I131 p131a l131d), (S131.filter (fun u131c => I131 u131c l131e)).card ≤ ((S131.filter (fun u131d => ¬ I131 u131d wz131 ∧ u131d ∉ Q131)).filter (fun u131e => I131 u131e l131e)).card + 1) := by
  intro q N r I _ S W hq hN hl hu
  refine ⟨?_, ?_⟩
  · intro pz T hT
    refine ⟨?_, ?_⟩
    · have hsub : (W \ W.filter (fun l => ¬ I pz l ∧ l ∉ T)) ⊆
          (Finset.univ.filter (fun l => I pz l)) ∪ T := by
        intro l hl'
        rw [Finset.mem_sdiff] at hl'
        rw [Finset.mem_union]
        by_cases h : I pz l
        · exact Or.inl (by simp [h])
        · by_cases h2 : l ∈ T
          · exact Or.inr h2
          · exact absurd (Finset.mem_filter.mpr ⟨hl'.1, h, h2⟩) hl'.2
      exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add (PEqualNP.Outside.L_meta_1719.deg_le q N I hq hN hl hu pz) hT))
    · intro l hlm
      simp only [Finset.mem_filter] at hlm
      obtain ⟨_, hpz, hlT⟩ := hlm
      have hsub : S.filter (fun u => I u l) ⊆
          ((S.filter (fun u => u ≠ pz ∧ ∀ m ∈ T, ¬ I u m)).filter (fun u => I u l)) ∪
            T.biUnion (fun m => Finset.univ.filter (fun u => I u m ∧ I u l)) := by
        intro u hu'
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ,
          true_and] at hu' ⊢
        by_cases h : ∃ m ∈ T, I u m
        · obtain ⟨m, hm, hm'⟩ := h
          exact Or.inr ⟨m, hm, hm', hu'.2⟩
        · refine Or.inl ⟨⟨hu'.1, ?_, fun m hm hI => h ⟨m, hm, hI⟩⟩, hu'.2⟩
          intro hupz
          exact hpz (hupz ▸ hu'.2)
      have hb : (T.biUnion (fun m => Finset.univ.filter (fun u => I u m ∧ I u l))).card
          ≤ T.card * 1 := by
        apply Finset.card_biUnion_le_card_mul
        intro m hm
        exact PEqualNP.Outside.L_meta_1719.meet_le_one N I hu m l (fun h => hlT (h ▸ hm))
      exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left (hb.trans (by omega)) _))
  · intro wz Q hQ
    refine ⟨?_, ?_⟩
    · have hsub : (W \ W.filter (fun l => l ≠ wz ∧ ∀ p ∈ Q, ¬ I p l)) ⊆
          {wz} ∪ Q.biUnion (fun p => Finset.univ.filter (fun l => I p l)) := by
        intro l hl'
        rw [Finset.mem_sdiff] at hl'
        rw [Finset.mem_union]
        by_cases h : l = wz
        · exact Or.inl (by simp [h])
        · by_cases h2 : ∃ p ∈ Q, I p l
          · obtain ⟨p, hp, hp'⟩ := h2
            exact Or.inr (Finset.mem_biUnion.mpr ⟨p, hp, by simp [hp']⟩)
          · exact absurd (Finset.mem_filter.mpr ⟨hl'.1, h, fun p hp hI => h2 ⟨p, hp, hI⟩⟩) hl'.2
      have hb : (Q.biUnion (fun p => Finset.univ.filter (fun l => I p l))).card
          ≤ Q.card * (q + 1) := by
        apply Finset.card_biUnion_le_card_mul
        intro p _
        exact PEqualNP.Outside.L_meta_1719.deg_le q N I hq hN hl hu p
      have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      rw [Finset.card_singleton] at h1
      exact h1.trans (Nat.add_le_add_left (hb.trans (Nat.mul_le_mul_right _ hQ)) 1)
    · intro l hlm
      simp only [Finset.mem_filter] at hlm
      obtain ⟨_, hne, hQl⟩ := hlm
      have hsub : S.filter (fun u => I u l) ⊆
          ((S.filter (fun u => ¬ I u wz ∧ u ∉ Q)).filter (fun u => I u l)) ∪
            Finset.univ.filter (fun u => I u wz ∧ I u l) := by
        intro u hu'
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and] at hu' ⊢
        by_cases h : I u wz
        · exact Or.inr ⟨h, hu'.2⟩
        · exact Or.inl ⟨⟨hu'.1, h, fun hq' => hQl u hq' hu'.2⟩, hu'.2⟩
      have hb := PEqualNP.Outside.L_meta_1719.meet_le_one N I hu wz l (Ne.symm hne)
      exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_left hb _))
