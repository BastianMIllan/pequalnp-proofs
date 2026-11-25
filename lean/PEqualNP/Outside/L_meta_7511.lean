import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7511 : ∀ (x1 x2 x3 : ℕ) (x4 : ℕ → Set ((Fin x1 → Bool) × (Fin x1 → Bool))),   let x5 : Type := (Fin x1 → Bool) × (Fin x1 → Bool);   have x6 : Fin x1 → Fin x1 → Bool := fun (x6 x7 : Fin x1) => Decidable.decide (x7 = x6);   x3 < x1 + x1 + x2 → (∀ (x8 : Fin x1), x4 ↑x8 = {x9 : x5 | x9.1 x8 = Bool.true} ∧ x4 (x1 + ↑x8) = {x9 : x5 | x9.2 x8 = Bool.true}) → (∀ x9 < x2, ∃ x11 < x1 + x1 + x9, ∃ x12 < x1 + x1 + x9, x4 (x1 + x1 + x9) = x4 x11 ∪ x4 x12 ∨ x4 (x1 + x1 + x9) = x4 x11 ∩ x4 x12) → (∀ (x10 : Fin x1), (x6 x10, fun (x11 : Fin x1) => Bool.false) ∉ x4 x3 ∧ (fun (x11 : Fin x1) => Bool.false, x6 x10) ∉ x4 x3) → ∃ (x11 : Finset ℕ), (∀ x12 ∈ x11, x12 < x2 ∧ ∃ x14 < x1 + x1 + x12, ∃ x15 < x1 + x1 + x12, x4 (x1 + x1 + x12) = x4 x14 ∩ x4 x15) ∧ ∀ (x12 : x5), x12 ∈ x4 x3 ↔ ∃ x13 ∈ x11, x12 ∈ x4 (x1 + x1 + x13) := by
  intro n m o S
  dsimp only
  intro ho hin hg hno
  have key : ∀ j, j < n + n + m →
      (∀ i : Fin n, ((fun x7 : Fin n => decide (x7 = i)), (fun _ : Fin n => false)) ∉ S j ∧
        ((fun _ : Fin n => false), (fun x7 : Fin n => decide (x7 = i))) ∉ S j) →
      ∃ T : Finset ℕ, (∀ k ∈ T, k < m ∧ ∃ a < n + n + k, ∃ b < n + n + k,
        S (n + n + k) = S a ∩ S b) ∧
        ∀ z, z ∈ S j ↔ ∃ k ∈ T, z ∈ S (n + n + k) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hnoj
      by_cases h1 : j < n
      · exfalso
        obtain ⟨i, rfl⟩ : ∃ i : Fin n, j = ↑i := ⟨⟨j, h1⟩, rfl⟩
        apply (hnoj i).1
        rw [(hin i).1]
        simp
      by_cases h2 : j < n + n
      · exfalso
        obtain ⟨i, rfl⟩ : ∃ i : Fin n, j = n + ↑i :=
          ⟨⟨j - n, by omega⟩, by show j = n + (j - n); omega⟩
        apply (hnoj i).2
        rw [(hin i).2]
        simp
      obtain ⟨k, rfl⟩ : ∃ k, j = n + n + k := ⟨j - (n + n), by omega⟩
      have hk : k < m := by omega
      obtain ⟨a, ha, b, hb, hcase⟩ := hg k hk
      rcases hcase with hu | hi
      · have hnoa : ∀ i : Fin n, ((fun x7 : Fin n => decide (x7 = i)), (fun _ : Fin n => false)) ∉ S a ∧
            ((fun _ : Fin n => false), (fun x7 : Fin n => decide (x7 = i))) ∉ S a := by
          intro i
          constructor
          · intro h
            exact (hnoj i).1 (by rw [hu]; exact Or.inl h)
          · intro h
            exact (hnoj i).2 (by rw [hu]; exact Or.inl h)
        have hnob : ∀ i : Fin n, ((fun x7 : Fin n => decide (x7 = i)), (fun _ : Fin n => false)) ∉ S b ∧
            ((fun _ : Fin n => false), (fun x7 : Fin n => decide (x7 = i))) ∉ S b := by
          intro i
          constructor
          · intro h
            exact (hnoj i).1 (by rw [hu]; exact Or.inr h)
          · intro h
            exact (hnoj i).2 (by rw [hu]; exact Or.inr h)
        obtain ⟨Ta, hTa, hma⟩ := ih a ha (by omega) hnoa
        obtain ⟨Tb, hTb, hmb⟩ := ih b hb (by omega) hnob
        refine ⟨Ta ∪ Tb, ?_, ?_⟩
        · intro k' hk'
          rcases Finset.mem_union.mp hk' with h | h
          · exact hTa k' h
          · exact hTb k' h
        · intro z
          rw [hu, Set.mem_union, hma z, hmb z]
          constructor
          · rintro (⟨k', hk', hz⟩ | ⟨k', hk', hz⟩)
            · exact ⟨k', Finset.mem_union_left _ hk', hz⟩
            · exact ⟨k', Finset.mem_union_right _ hk', hz⟩
          · rintro ⟨k', hk', hz⟩
            rcases Finset.mem_union.mp hk' with h | h
            · exact Or.inl ⟨k', h, hz⟩
            · exact Or.inr ⟨k', h, hz⟩
      · refine ⟨{k}, ?_, ?_⟩
        · intro k' hk'
          rw [Finset.mem_singleton] at hk'
          subst hk'
          exact ⟨hk, a, ha, b, hb, hi⟩
        · intro z
          constructor
          · intro hz
            exact ⟨k, Finset.mem_singleton_self k, hz⟩
          · rintro ⟨k', hk', hz⟩
            rw [Finset.mem_singleton] at hk'
            subst hk'
            exact hz
  exact key o ho hno
