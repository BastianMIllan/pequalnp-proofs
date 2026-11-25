import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6122

-- The family of sets meeting every member of a given family.
def blk (F : Set (Finset ℕ)) : Set (Finset ℕ) := {S | ∀ T ∈ F, ¬Disjoint T S}

theorem mem_blk (F : Set (Finset ℕ)) (S : Finset ℕ) : S ∈ blk F ↔ ∀ T ∈ F, ¬Disjoint T S :=
  Iff.rfl

theorem blk_image2 (F G : Set (Finset ℕ)) :
    blk (Set.image2 (fun (u v : Finset ℕ) => u ∪ v) F G) = blk F ∪ blk G := by
  ext S
  rw [Set.mem_union, mem_blk, mem_blk, mem_blk]
  constructor
  · intro hall
    by_contra hc
    rw [not_or] at hc
    obtain ⟨hc1, hc2⟩ := hc
    simp only [not_forall, not_not] at hc1 hc2
    obtain ⟨A, hA, hdA⟩ := hc1
    obtain ⟨C, hC, hdC⟩ := hc2
    exact hall (A ∪ C) ⟨A, hA, C, hC, rfl⟩ (Finset.disjoint_union_left.mpr ⟨hdA, hdC⟩)
  · rintro (h | h) _ ⟨A, hA, C, hC, rfl⟩ hd
    · have hd' : Disjoint (A ∪ C) S := hd
      exact h A hA (Finset.disjoint_union_left.mp hd').1
    · have hd' : Disjoint (A ∪ C) S := hd
      exact h C hC (Finset.disjoint_union_left.mp hd').2

theorem blk_union (F G : Set (Finset ℕ)) : blk (F ∪ G) = blk F ∩ blk G := by
  ext S
  rw [Set.mem_inter_iff, mem_blk, mem_blk, mem_blk]
  exact ⟨fun hall => ⟨fun T hT => hall T (Or.inl hT), fun T hT => hall T (Or.inr hT)⟩,
    fun ⟨h1, h2⟩ T hT => hT.elim (h1 T) (h2 T)⟩

theorem blk_empty : blk {∅} = ∅ := by
  ext S
  rw [mem_blk]
  simp

theorem blk_single (i : ℕ) : blk {{i}} = {x9 : Finset ℕ | i ∈ x9} := by
  ext S
  rw [mem_blk]
  simp

end PEqualNP.Outside.L_meta_6122

theorem PEqualNP.Outside.L_meta_6122 : ∀ (x1 x2 : ℕ) (x3 : ℕ → Set (Finset ℕ)), (∀ x4 < x1, x3 x4 = {{x4}}) → (∀ x5 < x2, ∃ x7 < x1 + x5, ∃ x8 < x1 + x5, x3 (x1 + x5) = Set.image2 (fun (x9 x10 : Finset ℕ) => x9 ∪ x10) (x3 x7) (x3 x8) ∨ x3 (x1 + x5) = x3 x7 ∨ x3 (x1 + x5) = {∅} ∨ x3 (x1 + x5) = x3 x7 ∪ x3 x8) → ∃ (x6 : ℕ → Set (Finset ℕ)), (∀ (x7 : ℕ) (x8 : Finset ℕ), x8 ∈ x6 x7 ↔ ∀ x9 ∈ x3 x7, ¬Disjoint x9 x8) ∧ (∀ x7 < x1, x6 x7 = {x9 : Finset ℕ | x7 ∈ x9}) ∧ ∀ x7 < x2, ∃ x9 < x1 + x7, ∃ x10 < x1 + x7, x6 (x1 + x7) ∈ [x6 x9 ∪ x6 x10, x6 x9 ∩ x6 x10, x6 x9, ∅] := by
  intro n m F hin hgate
  refine ⟨fun i => PEqualNP.Outside.L_meta_6122.blk (F i), fun i S => Iff.rfl, ?_, ?_⟩
  · intro i hi
    show PEqualNP.Outside.L_meta_6122.blk (F i) = _
    rw [hin i hi]
    exact PEqualNP.Outside.L_meta_6122.blk_single i
  · intro k hk
    obtain ⟨a, ha, b, hb, h⟩ := hgate k hk
    refine ⟨a, ha, b, hb, ?_⟩
    simp only [List.mem_cons]
    rcases h with h | h | h | h
    · left
      rw [h]
      exact PEqualNP.Outside.L_meta_6122.blk_image2 _ _
    · right; right; left
      rw [h]
    · right; right; right
      rw [h]
      exact Or.inl PEqualNP.Outside.L_meta_6122.blk_empty
    · right; left
      rw [h]
      exact PEqualNP.Outside.L_meta_6122.blk_union _ _
