import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7471 : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : Fin (13 : ℕ) → Fin ((13 : ℕ) + (13 : ℕ)) := fun (x2 : Fin (13 : ℕ)) => Fin.castAdd (13 : ℕ) x2; have x3 : Fin (13 : ℕ) → Fin ((13 : ℕ) + (13 : ℕ)) := fun (x3 : Fin (13 : ℕ)) => Fin.natAdd (13 : ℕ) x3; have x4 : (Fin (13 : ℕ) → Fin (26 : ℕ)) → Finset (Fin (26 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Fin (13 : ℕ) → Fin (26 : ℕ)) (x5 : Finset (Fin (26 : ℕ))) => {x6 : Fin (13 : ℕ) | x4 x6 ∉ x5}; have x5 : Finset (Fin (26 : ℕ)) → Prop := fun (x5 : Finset (Fin (26 : ℕ))) => ∀ (x6 x7 : Fin (13 : ℕ)), x1 x6 x7 → x2 x6 ∈ x5 ∨ x3 x7 ∈ x5; have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x6 : Finset (Fin (13 : ℕ))) => {x7 : Fin (13 : ℕ) | ∀ x8 ∈ x6, ¬x1 x8 x7}; ∀ (x7 : Set (Finset (Fin (26 : ℕ)))),   have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Prop := fun (x8 x9 : Finset (Fin (13 : ℕ))) => ∃ x10 ∈ x7, (∀ x11 ∈ x8, x2 x11 ∉ x10) ∧ ∀ x11 ∈ x9, x3 x11 ∉ x10;   (∀ (x9 x10 : Fin (13 : ℕ)), x1 x9 x10 → ¬x8 {x9} {x10}) → (∀ (x10 : Finset (Fin (13 : ℕ))), x10.card ≤ (3 : ℕ) → x8 x10 (x6 x10) ∧ x8 (x6 x10) x10) → (∀ x11 ∈ x7, x5 x11) ∧ ∀ (x11 : Finset (Fin (26 : ℕ))), Minimal x5 x11 → (x4 x2 x11).card ≤ (3 : ℕ) ∨ (x4 x3 x11).card ≤ (3 : ℕ) → x11 ∈ x7 := by
  dsimp only
  intro X h1 h2
  have cov : ∀ T ∈ X, ∀ p l : Fin 13, (p.val + l.val) % 13 ∈ [0, 1, 3, 9] →
      Fin.castAdd 13 p ∈ T ∨ Fin.natAdd 13 l ∈ T := by
    intro T hT p l hpl
    by_contra hc
    push_neg at hc
    apply h1 p l hpl
    refine ⟨T, hT, ?_, ?_⟩
    · intro a ha
      rw [Finset.mem_singleton.mp ha]
      exact hc.1
    · intro b hb
      rw [Finset.mem_singleton.mp hb]
      exact hc.2
  refine ⟨cov, ?_⟩
  intro S hmin hsmall
  have key : ∀ T ∈ X, T ⊆ S → S ∈ X := by
    intro T hT hTS
    have h3 : S ≤ T := hmin.le_of_le (cov T hT) hTS
    have hST : S = T := le_antisymm h3 hTS
    rw [hST]
    exact hT
  have split : ∀ v : Fin 26, (∃ p : Fin 13, v = Fin.castAdd 13 p) ∨
      (∃ l : Fin 13, v = Fin.natAdd 13 l) := by
    intro v
    have hv26 := v.isLt
    by_cases hlt : v.val < 13
    · exact Or.inl ⟨⟨v.val, hlt⟩, Fin.ext (by first | rfl | simp)⟩
    · refine Or.inr ⟨⟨v.val - 13, by omega⟩, Fin.ext ?_⟩
      first | (simp; omega) | simp | omega
  rcases hsmall with hA | hA
  · obtain ⟨T, hT, hT1, hT2⟩ := (h2 _ hA).1
    apply key T hT
    intro v hv
    rcases split v with ⟨p, rfl⟩ | ⟨l, rfl⟩
    · by_contra hp
      exact hT1 p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩) hv
    · by_contra hl
      apply hT2 l _ hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro a ha hR
      rcases hmin.prop a l hR with h | h
      · exact ha h
      · exact hl h
  · obtain ⟨T, hT, hT1, hT2⟩ := (h2 _ hA).2
    apply key T hT
    intro v hv
    rcases split v with ⟨p, rfl⟩ | ⟨l, rfl⟩
    · by_contra hp
      apply hT1 p _ hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro a ha hR
      have hR' : (p.val + a.val) % 13 ∈ [0, 1, 3, 9] := by rwa [Nat.add_comm]
      rcases hmin.prop p a hR' with h | h
      · exact hp h
      · exact ha h
    · by_contra hl
      exact hT2 l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩) hv
