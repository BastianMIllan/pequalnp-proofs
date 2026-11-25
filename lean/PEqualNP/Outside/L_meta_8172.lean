import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_8172 : ∀ (x1 x2 : List ℕ) (x3 : ℕ → ℕ → Bool) (x4 : ℕ) (x5 : List (ℕ × ℕ)),   have x6 : ℕ → Bool := fun (x6 : ℕ) => x5.any fun (x7 : ℕ × ℕ) => x3 x6 x7.1 && x3 x6 x7.2;   (∀ x7 ∈ x1, ∃ (x9 : Fin x4) (x10 : Fin x4), ∀ x11 ∈ x1 ++ x2, (x3 x11 ↑x9 && x3 x11 ↑x10) = Decidable.decide (x11 = x7)) → (∀ x8 ∈ x2, x6 x8 = Bool.false) → ∃ (x9 : List (ℕ × ℕ)), x9.length ≤ (List.filter (fun (x10 : ℕ) => !x6 x10) x1).length ∧ (∀ x10 ∈ x9, x10.1 < x4 ∧ x10.2 < x4) ∧ ∀ x10 ∈ x1 ++ x2, ((x5 ++ x9).any fun (x12 : ℕ × ℕ) => x3 x10 x12.1 && x3 x10 x12.2) = Decidable.decide (x10 ∈ x1) := by
  intro x1 x2 x3 x4 x5
  dsimp only
  intro h1 h2
  classical
  have hc : ∀ x7 : ℕ, ∃ p : ℕ × ℕ, x7 ∈ x1 → (p.1 < x4 ∧ p.2 < x4 ∧
      ∀ x11 ∈ x1 ++ x2, (x3 x11 p.1 && x3 x11 p.2) = decide (x11 = x7)) := by
    intro x7
    by_cases hm : x7 ∈ x1
    · obtain ⟨a, b, hab⟩ := h1 x7 hm
      exact ⟨(a.1, b.1), fun _ => ⟨a.2, b.2, hab⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hm⟩
  choose f hf using hc
  refine ⟨(List.filter (fun x10 => !(x5.any fun x7 => x3 x10 x7.1 && x3 x10 x7.2)) x1).map f,
    by simp, ?_, ?_⟩
  · intro p hp
    obtain ⟨x7, hx7, rfl⟩ := List.mem_map.mp hp
    have hm : x7 ∈ x1 := (List.mem_filter.mp hx7).1
    exact ⟨(hf x7 hm).1, (hf x7 hm).2.1⟩
  · intro x10 hx10
    rw [List.any_append]
    have key : (((List.filter (fun x10 => !(x5.any fun x7 => x3 x10 x7.1 && x3 x10 x7.2)) x1).map f).any
        fun x12 => x3 x10 x12.1 && x3 x10 x12.2) =
        decide (x10 ∈ List.filter (fun x10 => !(x5.any fun x7 => x3 x10 x7.1 && x3 x10 x7.2)) x1) := by
      apply Bool.eq_iff_iff.mpr
      rw [List.any_eq_true, decide_eq_true_iff]
      constructor
      · rintro ⟨p, hp, h⟩
        obtain ⟨x7, hx7, rfl⟩ := List.mem_map.mp hp
        have hm : x7 ∈ x1 := (List.mem_filter.mp hx7).1
        rw [(hf x7 hm).2.2 x10 hx10] at h
        have he : x10 = x7 := of_decide_eq_true h
        subst he
        exact hx7
      · intro h
        refine ⟨f x10, List.mem_map.mpr ⟨x10, h, rfl⟩, ?_⟩
        have hm : x10 ∈ x1 := (List.mem_filter.mp h).1
        rw [(hf x10 hm).2.2 x10 hx10]
        simp
    rw [key]
    by_cases hm : x10 ∈ x1
    · cases hb : (x5.any fun x7 => x3 x10 x7.1 && x3 x10 x7.2)
      · have : x10 ∈ List.filter (fun x10 => !(x5.any fun x7 => x3 x10 x7.1 && x3 x10 x7.2)) x1 :=
          List.mem_filter.mpr ⟨hm, by simp [hb]⟩
        simp [this, hm]
      · simp [hm]
    · have h2' : x10 ∈ x2 := by
        rcases List.mem_append.mp hx10 with h | h
        · exact absurd h hm
        · exact h
      have hb := h2 x10 h2'
      have hn : x10 ∉ List.filter (fun x10 => !(x5.any fun x7 => x3 x10 x7.1 && x3 x10 x7.2)) x1 :=
        fun h => hm (List.mem_filter.mp h).1
      rw [hb]
      simp [hn, hm]
