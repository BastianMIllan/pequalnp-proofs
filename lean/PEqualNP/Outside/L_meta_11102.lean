import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11102

-- Fooling set argument: six 0-entries, no two of which lie in one all-0 rectangle.

def rows : List ℕ := [589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008,
  38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921]

def fi : Fin 6 → Fin 20 := ![0, 1, 3, 6, 8, 11]
def fj : Fin 6 → Fin 20 := ![2, 7, 5, 12, 19, 4]

theorem fz : ∀ k : Fin 6, (rows.getD (fi k).val 0).testBit (fj k).val = false := by
  decide +kernel

theorem fx : ∀ a b : Fin 6, a ≠ b → (rows.getD (fi a).val 0).testBit (fj b).val = true ∨
    (rows.getD (fi b).val 0).testBit (fj a).val = true := by
  decide +kernel

theorem main (L : List (Finset (Fin 20) × Finset (Fin 20))) (hlen : L.length ≤ 5)
    (hz : ∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (rows.getD i.val 0).testBit j.val = false)
    (hc : ∀ (i : Fin 20) (j : Fin 20), (rows.getD i.val 0).testBit j.val = false →
      ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) : False := by
  classical
  choose g hg using fun k : Fin 6 => hc (fi k) (fj k) (fz k)
  have inj : Function.Injective g := by
    intro a b hab
    by_contra hne
    rcases fx a b hne with h | h
    · have h2 : fj b ∈ (g a).2 := by rw [hab]; exact (hg b).2.2
      have := hz (g a) (hg a).1 (fi a) (hg a).2.1 (fj b) h2
      rw [h] at this
      exact Bool.noConfusion this
    · have h2 : fj a ∈ (g b).2 := by rw [← hab]; exact (hg a).2.2
      have := hz (g b) (hg b).1 (fi b) (hg b).2.1 (fj a) h2
      rw [h] at this
      exact Bool.noConfusion this
  have hsub : Finset.univ.image g ⊆ L.toFinset := by
    intro r hr
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hr
    exact List.mem_toFinset.2 (hg k).1
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_fin] at h1
  have h2 := List.toFinset_card_le L
  omega

end PEqualNP.Outside.L_meta_11102

theorem PEqualNP.Outside.L_meta_11102 : ¬ (∃ L : List (Finset (Fin 20) × Finset (Fin 20)), L.length ≤ 5 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 20) (j : Fin 20), (([589842, 131109, 262218, 524436, 297, 594, 1188, 2376, 4752, 9504, 19008, 38016, 76032, 152064, 304128, 608256, 167937, 335874, 671748, 294921] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L, hlen, hz, hc⟩
  exact PEqualNP.Outside.L_meta_11102.main L hlen hz hc
