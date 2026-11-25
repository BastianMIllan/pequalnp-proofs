import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10039

def L : List (Finset (Fin 16) × Finset (Fin 20)) :=
  [({0, 2, 6, 7, 12, 15}, {1, 5, 11, 15, 18}),
   ({0, 3, 4, 5, 9, 11}, {2, 6, 9, 13, 19}),
   ({0, 1, 8, 10, 13, 14}, {3, 7, 10, 14, 17}),
   ({2, 3, 5, 7, 9, 10}, {0, 5, 8, 13, 19}),
   ({4, 6, 8, 9, 13, 14}, {3, 4, 9, 14, 16}),
   ({1, 3, 8, 11, 12, 13}, {2, 4, 10, 12, 17}),
   ({4, 10, 11, 15}, {1, 6, 7, 11, 12, 16}),
   ({5, 12, 14}, {3, 6, 8, 10, 13, 15, 16, 18}),
   ({1, 9, 15}, {0, 2, 6, 8, 11, 14, 15, 17}),
   ({7, 8}, {1, 2, 4, 5, 7, 8, 10, 14, 15, 16, 19}),
   ({2, 13}, {0, 3, 4, 5, 7, 9, 11, 12, 13, 17, 18}),
   ({1, 3, 5, 6}, {0, 6, 10, 12, 18, 19}),
   ({3, 4, 14, 15}, {1, 6, 8, 9, 14, 18}),
   ({5, 11, 14}, {0, 6, 7, 9, 10, 13, 15, 16})]

theorem hlen : L.length ≤ 14 := by decide

theorem hzero : ∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([69905, 74274, 83012, 100488, 164897, 149522, 139652, 135752, 272449, 267394, 295444, 278824, 541313, 557378, 530468, 533528] : List ℕ).getD i.val 0).testBit j.val = false := by
  unfold L
  repeat' (first | exact List.forall_mem_nil _ | refine List.forall_mem_cons.2 ⟨by decide +kernel, ?_⟩)

theorem hcov : ∀ (i : Fin 16) (j : Fin 20), (([69905, 74274, 83012, 100488, 164897, 149522, 139652, 135752, 272449, 267394, 295444, 278824, 541313, 557378, 530468, 533528] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  intro i
  fin_cases i <;> decide +kernel

end PEqualNP.Outside.L_meta_10039

theorem PEqualNP.Outside.L_meta_10039 : ∃ L : List (Finset (Fin 16) × Finset (Fin 20)), L.length ≤ 14 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([69905, 74274, 83012, 100488, 164897, 149522, 139652, 135752, 272449, 267394, 295444, 278824, 541313, 557378, 530468, 533528] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 16) (j : Fin 20), (([69905, 74274, 83012, 100488, 164897, 149522, 139652, 135752, 272449, 267394, 295444, 278824, 541313, 557378, 530468, 533528] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  exact ⟨PEqualNP.Outside.L_meta_10039.L, PEqualNP.Outside.L_meta_10039.hlen, PEqualNP.Outside.L_meta_10039.hzero, PEqualNP.Outside.L_meta_10039.hcov⟩
