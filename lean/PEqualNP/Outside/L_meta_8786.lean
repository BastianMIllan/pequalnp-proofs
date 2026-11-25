import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_8786 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 6) (v : Fin 4) => (13124385 : ℕ).testBit (4 * u.val + v.val)) 11 := by
  let C : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [7, 11]⟩, ⟨.or, [4, 5]⟩,
    ⟨.and, [6, 10]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [12, 16]⟩,
    ⟨.and, [8, 17]⟩, ⟨.or, [18, 19]⟩], 20⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
