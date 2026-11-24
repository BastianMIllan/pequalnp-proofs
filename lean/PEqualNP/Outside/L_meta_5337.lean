import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5337

-- peeling: drop low-degree vertices until every remaining vertex has degree above k
theorem key (n k : ℕ) (E : Finset (Fin n × Fin n)) : ∀ s : ℕ, ∀ A B : Finset (Fin n),
    A.card + B.card = s →
    k * (A.card + B.card) < (E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B)).card →
    ∃ X Y : Finset (Fin n), X.Nonempty ∧ Y.Nonempty ∧
      (∀ x ∈ X, k < (Y.filter (fun y => (x, y) ∈ E)).card) ∧
      ∀ y ∈ Y, k < (X.filter (fun x => (x, y) ∈ E)).card := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro A B hs hlt
  by_cases hA : ∃ a ∈ A, (B.filter (fun y => (a, y) ∈ E)).card ≤ k
  · obtain ⟨a, ha, hdeg⟩ := hA
    have hpos := Finset.card_pos.mpr ⟨a, ha⟩
    have hce := Finset.card_erase_of_mem ha
    apply ih ((A.erase a).card + B.card) (by omega) (A.erase a) B rfl
    have hsub : E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B) ⊆
        E.filter (fun e => e.1 ∈ A.erase a ∧ e.2 ∈ B) ∪
          (B.filter (fun y => (a, y) ∈ E)).image (fun y => (a, y)) := by
      intro e he
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_erase] at he ⊢
      by_cases h : e.1 = a
      · right
        refine ⟨e.2, ⟨he.2.2, ?_⟩, ?_⟩
        · rw [← h]; exact he.1
        · ext <;> simp [h]
      · left
        exact ⟨he.1, ⟨h, he.2.1⟩, he.2.2⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (E.filter (fun e => e.1 ∈ A.erase a ∧ e.2 ∈ B))
      ((B.filter (fun y => (a, y) ∈ E)).image (fun y => (a, y)))
    have h3 := Finset.card_image_le (s := B.filter (fun y => (a, y) ∈ E)) (f := fun y => (a, y))
    have hk : k * ((A.erase a).card + B.card) + k = k * (A.card + B.card) := by
      rw [← Nat.mul_succ]; congr 1; omega
    generalize k * ((A.erase a).card + B.card) = P at hk ⊢
    generalize k * (A.card + B.card) = Q at hk hlt
    omega
  push_neg at hA
  by_cases hB : ∃ b ∈ B, (A.filter (fun x => (x, b) ∈ E)).card ≤ k
  · obtain ⟨b, hb, hdeg⟩ := hB
    have hpos := Finset.card_pos.mpr ⟨b, hb⟩
    have hce := Finset.card_erase_of_mem hb
    apply ih (A.card + (B.erase b).card) (by omega) A (B.erase b) rfl
    have hsub : E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B) ⊆
        E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B.erase b) ∪
          (A.filter (fun x => (x, b) ∈ E)).image (fun x => (x, b)) := by
      intro e he
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image, Finset.mem_erase] at he ⊢
      by_cases h : e.2 = b
      · right
        refine ⟨e.1, ⟨he.2.1, ?_⟩, ?_⟩
        · rw [← h]; exact he.1
        · ext <;> simp [h]
      · left
        exact ⟨he.1, he.2.1, ⟨h, he.2.2⟩⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B.erase b))
      ((A.filter (fun x => (x, b) ∈ E)).image (fun x => (x, b)))
    have h3 := Finset.card_image_le (s := A.filter (fun x => (x, b) ∈ E)) (f := fun x => (x, b))
    have hk : k * (A.card + (B.erase b).card) + k = k * (A.card + B.card) := by
      rw [← Nat.mul_succ]; congr 1; omega
    generalize k * (A.card + (B.erase b).card) = P at hk ⊢
    generalize k * (A.card + B.card) = Q at hk hlt
    omega
  push_neg at hB
  have hne : (E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B)).Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨e, he⟩ := hne
  simp only [Finset.mem_filter] at he
  exact ⟨A, B, ⟨e.1, he.2.1⟩, ⟨e.2, he.2.2⟩, hA, hB⟩

end PEqualNP.Outside.L_meta_5337

theorem PEqualNP.Outside.L_meta_5337 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x1)), x2 * (x1 + x1) < x3.card → ∃ (x5 : Finset (Fin x1)) (x6 : Finset (Fin x1)), x5.Nonempty ∧ x6.Nonempty ∧ (∀ x7 ∈ x5, x2 < {x9 ∈ x6 | (x7, x9) ∈ x3}.card) ∧ ∀ x7 ∈ x6, x2 < {x9 ∈ x5 | (x9, x7) ∈ x3}.card := by
  intro x1 x2 x3 h
  apply PEqualNP.Outside.L_meta_5337.key x1 x2 x3 _ Finset.univ Finset.univ rfl
  simp only [Finset.mem_univ, and_self, Finset.filter_true_of_mem, implies_true,
    Finset.card_univ, Fintype.card_fin]
  exact h
