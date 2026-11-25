import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7608

theorem locate {α : Type} (x2 x3 : List (Set α)) (x4 : Set α) (hx2 : ∀ x7 ∈ x2, ¬x7 ⊆ x4)
    (k : ℕ) (a : Set α) (ha : a ∈ x2 ++ List.take k x3) (hsub : a ⊆ x4) :
    ∃ j, ∃ hj : j < x3.length, j < k ∧ x3.get ⟨j, hj⟩ = a := by
  rcases List.mem_append.1 ha with h | h
  · exact absurd hsub (hx2 a h)
  · obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.1 h
    have hi' : i < min k x3.length := by simpa using hi
    refine ⟨i, by omega, by omega, ?_⟩
    rw [← hia]
    simp

theorem main {α : Type} (x2 x3 : List (Set α)) (x4 : Set α) (hx2 : ∀ x7 ∈ x2, ¬x7 ⊆ x4)
    (hgen : ∀ (x8 : Fin x3.length), ∃ x9 ∈ x2 ++ List.take (↑x8) x3, ∃ x10 ∈ x2 ++ List.take (↑x8) x3,
      x3.get x8 = x9 ∪ x10 ∨ x3.get x8 = x9 ∩ x10) (x9 : α) :
    ∀ (k : ℕ) (hk : k < x3.length), x3.get ⟨k, hk⟩ ⊆ x4 → x9 ∈ x3.get ⟨k, hk⟩ →
      ∃ (x11 : Fin x3.length), x3.get x11 ⊆ x4 ∧ x9 ∈ x3.get x11 ∧
        ∃ x12 ∈ x2 ++ List.take (↑x11) x3, ∃ x13 ∈ x2 ++ List.take (↑x11) x3,
          ¬x12 ⊆ x4 ∧ ¬x13 ⊆ x4 ∧ x3.get x11 = x12 ∩ x13 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hsub hin
    obtain ⟨a, ha, b, hb, hab⟩ := hgen ⟨k, hk⟩
    rcases hab with hu | hi
    · rw [hu] at hsub hin
      rcases hin with hina | hinb
      · have hasub : a ⊆ x4 := fun y hy => hsub (Or.inl hy)
        obtain ⟨j, hj, hjk, hja⟩ := locate x2 x3 x4 hx2 k a ha hasub
        exact ih j hjk hj (by rw [hja]; exact hasub) (by rw [hja]; exact hina)
      · have hbsub : b ⊆ x4 := fun y hy => hsub (Or.inr hy)
        obtain ⟨j, hj, hjk, hjb⟩ := locate x2 x3 x4 hx2 k b hb hbsub
        exact ih j hjk hj (by rw [hjb]; exact hbsub) (by rw [hjb]; exact hinb)
    · by_cases hasub : a ⊆ x4
      · obtain ⟨j, hj, hjk, hja⟩ := locate x2 x3 x4 hx2 k a ha hasub
        have hina : x9 ∈ a := by rw [hi] at hin; exact hin.1
        exact ih j hjk hj (by rw [hja]; exact hasub) (by rw [hja]; exact hina)
      · by_cases hbsub : b ⊆ x4
        · obtain ⟨j, hj, hjk, hjb⟩ := locate x2 x3 x4 hx2 k b hb hbsub
          have hinb : x9 ∈ b := by rw [hi] at hin; exact hin.2
          exact ih j hjk hj (by rw [hjb]; exact hbsub) (by rw [hjb]; exact hinb)
        · exact ⟨⟨k, hk⟩, hsub, hin, a, ha, b, hb, hasub, hbsub, hi⟩

end PEqualNP.Outside.L_meta_7608

theorem PEqualNP.Outside.L_meta_7608 : ∀ (x1 : Type) (x2 x3 : List (Set x1)) (x4 : Set x1),   have x5 : ℕ → List (Set x1) := fun (x5 : ℕ) => x2 ++ List.take x5 x3;   x4 ∈ x2 ++ x3 → (∀ x7 ∈ x2, ¬x7 ⊆ x4) → (∀ (x8 : Fin x3.length), ∃ x9 ∈ x5 ↑x8, ∃ x10 ∈ x5 ↑x8, x3.get x8 = x9 ∪ x10 ∨ x3.get x8 = x9 ∩ x10) → ∀ x9 ∈ x4, ∃ (x11 : Fin x3.length), x3.get x11 ⊆ x4 ∧ x9 ∈ x3.get x11 ∧ ∃ x12 ∈ x5 ↑x11, ∃ x13 ∈ x5 ↑x11, ¬x12 ⊆ x4 ∧ ¬x13 ⊆ x4 ∧ x3.get x11 = x12 ∩ x13 := by
  intro x1 x2 x3 x4
  intro x5 hmem hx2 hgen x9 hx9
  have hlast := PEqualNP.Outside.L_meta_7608.locate x2 x3 x4 hx2 x3.length x4
    (by simpa using hmem) (fun _ h => h)
  obtain ⟨k, hk, _, hkx⟩ := hlast
  exact PEqualNP.Outside.L_meta_7608.main x2 x3 x4 hx2 hgen x9 k hk
    (by rw [hkx]) (by rw [hkx]; exact hx9)
