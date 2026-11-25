import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6878

-- one endpoint of each matching edge (i, i + 21), chosen inside the cover
def pick (s : Finset (Fin 42)) (i : Fin 21) : Fin 42 :=
  if (⟨i.val, by omega⟩ : Fin 42) ∈ s then ⟨i.val, by omega⟩ else ⟨i.val + 21, by omega⟩

theorem pick_inj (s : Finset (Fin 42)) : Function.Injective (pick s) := by
  intro a b hab
  unfold pick at hab
  apply Fin.ext
  split_ifs at hab <;> simp only [Fin.mk.injEq] at hab <;> omega

end PEqualNP.Outside.L_meta_6878

theorem PEqualNP.Outside.L_meta_6878 : let x1 : Fin (42 : ℕ) × Fin (42 : ℕ) → Prop := fun (x1 : Fin (42 : ℕ) × Fin (42 : ℕ)) => ↑x1.1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x1.2 ∧ (↑x1.2 + (21 : ℕ) - ↑x1.1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : Finset (Fin (42 : ℕ) × Fin (42 : ℕ)) := Finset.filter x1 Finset.univ; ∀ (x3 : Finset (Fin (42 : ℕ))), (∀ x4 ∈ x2, x4.1 ∈ x3 ∨ x4.2 ∈ x3) → (21 : ℕ) ≤ x3.card := by
  dsimp only
  intro s h
  have key : ∀ i : Fin 21, (⟨i.val, by omega⟩ : Fin 42) ∈ s ∨ (⟨i.val + 21, by omega⟩ : Fin 42) ∈ s := by
    intro i
    apply h (⟨i.val, by omega⟩, ⟨i.val + 21, by omega⟩)
    rw [Finset.mem_filter]
    have e : (i.val + 21 + 21 - i.val) % 21 = 0 := by omega
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · show i.val < 21
      exact i.isLt
    · show 21 ≤ i.val + 21
      omega
    · show (i.val + 21 + 21 - i.val) % 21 ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]
      rw [e]
      simp
  have hmem : ∀ i : Fin 21, PEqualNP.Outside.L_meta_6878.pick s i ∈ s := by
    intro i
    unfold PEqualNP.Outside.L_meta_6878.pick
    split_ifs with hc
    · exact hc
    · exact (key i).resolve_left hc
  calc (21 : ℕ) = (Finset.univ.image (PEqualNP.Outside.L_meta_6878.pick s)).card := by
          rw [Finset.card_image_of_injective _ (PEqualNP.Outside.L_meta_6878.pick_inj s)]
          simp
    _ ≤ s.card := by
          apply Finset.card_le_card
          intro y hy
          rw [Finset.mem_image] at hy
          obtain ⟨i, _, rfl⟩ := hy
          exact hmem i
