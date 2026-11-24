import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2998

abbrev Shape (x2 : ℕ) (x6 : ℕ → Set (Finset ℕ)) (k : ℕ) : Prop :=
  ∃ x9 < x2 + k, ∃ x10 < x2 + k,
    x6 (x2 + k) = Set.image2 (fun (x11 x12 : Finset ℕ) => x11 ∪ x12) (x6 x9) (x6 x10) ∨
    x6 (x2 + k) = x6 x9 ∨ x6 (x2 + k) = {∅} ∨ x6 (x2 + k) = x6 x9 ∪ x6 x10

abbrev Good {α : Type} (x2 : ℕ) (x4 : ℕ → Set α) (F : Set (Finset ℕ)) (k : ℕ) : Prop :=
  (∀ x9 ∈ F, ∀ x11 ∈ x9, x11 < x2) ∧
    ∀ (x9 : α), x9 ∉ x4 k ↔ ∃ x10 ∈ F, ∀ x11 ∈ x10, x9 ∉ x4 x11

abbrev Inv {α : Type} (x2 n : ℕ) (x4 : ℕ → Set α) (x6 : ℕ → Set (Finset ℕ)) : Prop :=
  (∀ k < x2, x6 k = {{k}}) ∧ (∀ k < n, Shape x2 x6 k) ∧ ∀ k < x2 + n, Good x2 x4 (x6 k) k

theorem base {α : Type} (x2 : ℕ) (x4 : ℕ → Set α) :
    Inv x2 0 x4 (fun k => {{k}}) := by
  refine ⟨fun k _ => rfl, fun k hk => absurd hk (Nat.not_lt_zero _), fun k hk => ⟨?_, ?_⟩⟩
  · intro S hS i hi
    simp only [Set.mem_singleton_iff] at hS
    subst hS
    rw [Finset.mem_singleton] at hi
    omega
  · intro y
    simp

theorem step {α : Type} (x2 n : ℕ) (x4 : ℕ → Set α) (x6 : ℕ → Set (Finset ℕ))
    (hinv : Inv x2 n x4 x6) (F : Set (Finset ℕ))
    (hF : ∃ a < x2 + n, ∃ b < x2 + n,
      F = Set.image2 (fun (x11 x12 : Finset ℕ) => x11 ∪ x12) (x6 a) (x6 b) ∨
      F = x6 a ∨ F = {∅} ∨ F = x6 a ∪ x6 b)
    (hG : Good x2 x4 F (x2 + n)) :
    Inv x2 (n + 1) x4 (fun k => if k = x2 + n then F else x6 k) := by
  obtain ⟨h1, h2, h3⟩ := hinv
  have hag : ∀ j < x2 + n, (if j = x2 + n then F else x6 j) = x6 j :=
    fun j hj => if_neg (by omega)
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · dsimp only
    rw [hag k (by omega)]
    exact h1 k hk
  · by_cases hk' : k < n
    · obtain ⟨a, ha, b, hb, h⟩ := h2 k hk'
      refine ⟨a, ha, b, hb, ?_⟩
      dsimp only
      rw [hag (x2 + k) (by omega), hag a (by omega), hag b (by omega)]
      exact h
    · obtain rfl : k = n := by omega
      obtain ⟨a, ha, b, hb, h⟩ := hF
      refine ⟨a, ha, b, hb, ?_⟩
      dsimp only
      rw [if_pos rfl, hag a ha, hag b hb]
      exact h
  · by_cases hk' : k < x2 + n
    · dsimp only
      rw [hag k hk']
      exact h3 k hk'
    · obtain rfl : k = x2 + n := by omega
      dsimp only
      rw [if_pos rfl]
      exact hG

end PEqualNP.Outside.L_meta_2998

theorem PEqualNP.Outside.L_meta_2998 : ∀ (x1 : Type) (x2 x3 : ℕ) (x4 : ℕ → Set x1), (∀ x5 < x3, ∃ x7 < x2 + x5, ∃ x8 < x2 + x5, x4 (x2 + x5) = x4 x7 ∪ x4 x8 ∨ x4 (x2 + x5) = x4 x7 ∨ x4 (x2 + x5) = ∅ ∨ x4 (x2 + x5) = x4 x7 ∩ x4 x8) → ∃ (x6 : ℕ → Set (Finset ℕ)), (∀ x7 < x2, x6 x7 = {{x7}}) ∧ (∀ x7 < x3, ∃ x9 < x2 + x7, ∃ x10 < x2 + x7, x6 (x2 + x7) = Set.image2 (fun (x11 x12 : Finset ℕ) => x11 ∪ x12) (x6 x9) (x6 x10) ∨ x6 (x2 + x7) = x6 x9 ∨ x6 (x2 + x7) = {∅} ∨ x6 (x2 + x7) = x6 x9 ∪ x6 x10) ∧ ∀ x7 < x2 + x3, (∀ x9 ∈ x6 x7, ∀ x11 ∈ x9, x11 < x2) ∧ ∀ (x9 : x1), x9 ∉ x4 x7 ↔ ∃ x10 ∈ x6 x7, ∀ x11 ∈ x10, x9 ∉ x4 x11 := by
  intro x1 x2 x3 x4 hx
  have key : ∀ n ≤ x3, ∃ x6, PEqualNP.Outside.L_meta_2998.Inv x2 n x4 x6 := by
    intro n
    induction n with
    | zero => intro _; exact ⟨_, PEqualNP.Outside.L_meta_2998.base x2 x4⟩
    | succ n ih =>
      intro hn
      obtain ⟨x6, hinv⟩ := ih (by omega)
      obtain ⟨a, ha, b, hb, hc⟩ := hx n (by omega)
      have hb3 := hinv.2.2
      have ga := hb3 a (by omega)
      have gb := hb3 b (by omega)
      rcases hc with hc | hc | hc | hc
      · refine ⟨_, PEqualNP.Outside.L_meta_2998.step x2 n x4 x6 hinv
          (Set.image2 (fun (x11 x12 : Finset ℕ) => x11 ∪ x12) (x6 a) (x6 b))
          ⟨a, ha, b, hb, Or.inl rfl⟩ ⟨?_, ?_⟩⟩
        · rintro S ⟨S1, hS1, S2, hS2, rfl⟩ i hi
          rcases Finset.mem_union.mp hi with hi | hi
          · exact ga.1 S1 hS1 i hi
          · exact gb.1 S2 hS2 i hi
        · intro y
          rw [hc, Set.mem_union, not_or]
          constructor
          · rintro ⟨hy1, hy2⟩
            obtain ⟨S1, hS1, k1⟩ := (ga.2 y).mp hy1
            obtain ⟨S2, hS2, k2⟩ := (gb.2 y).mp hy2
            refine ⟨S1 ∪ S2, Set.mem_image2_of_mem hS1 hS2, fun i hi => ?_⟩
            rcases Finset.mem_union.mp hi with hi | hi
            exacts [k1 i hi, k2 i hi]
          · rintro ⟨S, ⟨S1, hS1, S2, hS2, rfl⟩, k⟩
            exact ⟨(ga.2 y).mpr ⟨S1, hS1, fun i hi => k i (Finset.mem_union_left _ hi)⟩,
              (gb.2 y).mpr ⟨S2, hS2, fun i hi => k i (Finset.mem_union_right _ hi)⟩⟩
      · refine ⟨_, PEqualNP.Outside.L_meta_2998.step x2 n x4 x6 hinv (x6 a)
          ⟨a, ha, b, hb, Or.inr (Or.inl rfl)⟩ ⟨ga.1, fun y => ?_⟩⟩
        rw [hc]
        exact ga.2 y
      · refine ⟨_, PEqualNP.Outside.L_meta_2998.step x2 n x4 x6 hinv {∅}
          ⟨a, ha, b, hb, Or.inr (Or.inr (Or.inl rfl))⟩ ⟨?_, fun y => ?_⟩⟩
        · intro S hS i hi
          rw [Set.mem_singleton_iff] at hS
          subst hS
          simp at hi
        · rw [hc]
          simp
      · refine ⟨_, PEqualNP.Outside.L_meta_2998.step x2 n x4 x6 hinv (x6 a ∪ x6 b)
          ⟨a, ha, b, hb, Or.inr (Or.inr (Or.inr rfl))⟩ ⟨?_, fun y => ?_⟩⟩
        · rintro S (hS | hS) i hi
          · exact ga.1 S hS i hi
          · exact gb.1 S hS i hi
        · rw [hc, Set.mem_inter_iff, not_and_or]
          constructor
          · rintro (hy | hy)
            · obtain ⟨S, hS, k⟩ := (ga.2 y).mp hy
              exact ⟨S, Or.inl hS, k⟩
            · obtain ⟨S, hS, k⟩ := (gb.2 y).mp hy
              exact ⟨S, Or.inr hS, k⟩
          · rintro ⟨S, hS | hS, k⟩
            · exact Or.inl ((ga.2 y).mpr ⟨S, hS, k⟩)
            · exact Or.inr ((gb.2 y).mpr ⟨S, hS, k⟩)
  obtain ⟨x6, h1, h2, h3⟩ := key x3 le_rfl
  exact ⟨x6, h1, h2, fun k hk => h3 k hk⟩
