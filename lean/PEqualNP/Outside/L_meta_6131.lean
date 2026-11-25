import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6131

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- the graph is complete: one AND of no wires is constantly true
def C1 : Circuit :=
  { gates := [{ op := GateOp.and, inputs := [] }], output := 8 }

lemma upper : RepSizeAtMost (fun u v : Fin 4 => (65535 : ℕ).testBit (4 * u.val + v.val)) 1 := by
  refine ⟨C1, ?_, by decide, by decide⟩
  intro g hg
  simp only [C1, List.mem_cons, List.not_mem_nil, or_false] at hg
  subst hg
  simp

lemma getD_none (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

-- with no gates the output is a single input wire (or false), which cannot be true at
-- both (0, 0) and (1, 1)
lemma lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (65535 : ℕ).testBit (4 * u.val + v.val)) 0 := by
  rintro ⟨⟨gs, o⟩, _, hs, hr⟩
  have hs' : gs.length ≤ 0 := hs
  rcases gs with _ | ⟨g, gs⟩
  · have h1 := hr 0 0
    have h2 := hr 1 1
    simp only [Circuit.eval, Circuit.wires, List.foldl_nil] at h1 h2
    by_cases ho : o < 8
    · interval_cases o <;> revert h1 h2 <;> decide
    · rw [getD_none _ _ (by simp only [oneEach, List.length_append, List.length_ofFn]; omega)]
        at h1
      revert h1; decide
  · simp only [List.length_cons] at hs'; omega

end PEqualNP.Outside.L_meta_6131

theorem PEqualNP.Outside.L_meta_6131 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (65535 : ℕ).testBit (4 * u.val + v.val)) 1 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (65535 : ℕ).testBit (4 * u.val + v.val)) 0 :=
  ⟨PEqualNP.Outside.L_meta_6131.upper, PEqualNP.Outside.L_meta_6131.lower⟩
