import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9985

-- Fourteen all-1 rectangles covering the 1-entries (found by exhaustive search over maximal rectangles).
def cover : List (Finset (Fin 15) × Finset (Fin 15)) := [
    ({0}, {9, 10, 11, 12, 13, 14}),
    ({1, 3, 10}, {6, 8, 13}),
    ({1, 2, 9}, {7, 8, 14}),
    ({1, 4, 11}, {6, 7, 12}),
    ({2, 3, 12}, {5, 8, 11}),
    ({2, 4, 13}, {5, 7, 10}),
    ({3, 4, 14}, {5, 6, 9}),
    ({5, 7, 10}, {2, 4, 13}),
    ({5, 6, 9}, {3, 4, 14}),
    ({5, 8, 11}, {2, 3, 12}),
    ({6, 7, 12}, {1, 4, 11}),
    ({6, 8, 13}, {1, 3, 10}),
    ({7, 8, 14}, {1, 2, 9}),
    ({9, 10, 11, 12, 13, 14}, {0})]

end PEqualNP.Outside.L_meta_9985

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_9985 : ∃ L : List (Finset (Fin 15) × Finset (Fin 15)), L.length ≤ 14 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([32256, 29120, 19872, 11104, 5856, 28700, 19482, 10774, 5646, 16793, 8533, 4301, 2355, 1195, 615] : List ℕ).getD i.val 0).testBit j.val = true) ∧ ∀ (i : Fin 15) (j : Fin 15), (([32256, 29120, 19872, 11104, 5856, 28700, 19482, 10774, 5646, 16793, 8533, 4301, 2355, 1195, 615] : List ℕ).getD i.val 0).testBit j.val = true → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  let L := PEqualNP.Outside.L_meta_9985.cover
  let M : List ℕ := [32256, 29120, 19872, 11104, 5856, 28700, 19482, 10774, 5646, 16793, 8533, 4301, 2355, 1195, 615]
  have sound : ∀ k : Fin L.length, ∀ i j : Fin 15, i ∈ (L.get k).1 → j ∈ (L.get k).2 →
      (M.getD i.val 0).testBit j.val = true := by decide +kernel
  have hits : ∀ i j : Fin 15, (M.getD i.val 0).testBit j.val = true →
      ∃ k : Fin L.length, i ∈ (L.get k).1 ∧ j ∈ (L.get k).2 := by decide +kernel
  refine ⟨L, by decide, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hr
    exact sound k i j hi hj
  · intro i j h
    obtain ⟨k, hi, hj⟩ := hits i j h
    exact ⟨L.get k, List.get_mem L k, hi, hj⟩
