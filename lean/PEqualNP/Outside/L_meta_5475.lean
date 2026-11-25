import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5475

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 4 → Bool := fun u v => (255 : ℕ).testBit (4 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 1] }], output := 8 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  subst hg
  simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

theorem small_out : ∀ o : Fin 8,
    ¬ ((PEqualNP.Represents.oneEach (0 : Fin 4) (0 : Fin 4)).getD o.val false = A 0 0 ∧
      (PEqualNP.Represents.oneEach (1 : Fin 4) (0 : Fin 4)).getD o.val false = A 1 0 ∧
      (PEqualNP.Represents.oneEach (0 : Fin 4) (1 : Fin 4)).getD o.val false = A 0 1) := by
  decide +kernel

theorem oneEach_len (u v : Fin 4) : (PEqualNP.Represents.oneEach u v).length = 8 := by
  simp [PEqualNP.Represents.oneEach]

theorem A_vals : A 0 0 = true ∧ A 1 0 = true ∧ A 0 1 = true := by
  decide +kernel

theorem no_zero (C : Circuit) (hs : C.size ≤ 0) (hr : PEqualNP.Represents.Represents A C) :
    False := by
  have hg : C.gates = [] := List.length_eq_zero_iff.mp (by
    have := hs
    simp only [Circuit.size] at this
    omega)
  have e : ∀ x, C.eval x = x.getD C.output false := by
    intro x
    simp [Circuit.eval, Circuit.wires, hg]
  have h1 := hr 0 0
  have h2 := hr 1 0
  have h3 := hr 0 1
  rw [e] at h1 h2 h3
  by_cases ho : C.output < 8
  · exact small_out ⟨C.output, ho⟩ ⟨h1, h2, h3⟩
  · have hl : (PEqualNP.Represents.oneEach (0 : Fin 4) (0 : Fin 4)).length ≤ C.output := by
      rw [oneEach_len]
      omega
    rw [List.getD_eq_default _ _ hl] at h1
    rw [A_vals.1] at h1
    exact Bool.noConfusion h1

end PEqualNP.Outside.L_meta_5475

theorem PEqualNP.Outside.L_meta_5475 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (255 : ℕ).testBit (4 * u.val + v.val)) 1 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (255 : ℕ).testBit (4 * u.val + v.val)) 0 := by
  refine ⟨⟨PEqualNP.Outside.L_meta_5475.upperC, PEqualNP.Outside.L_meta_5475.upper_mono,
    by decide, PEqualNP.Outside.L_meta_5475.upper_rep⟩, ?_⟩
  rintro ⟨C, _, hs, hr⟩
  exact PEqualNP.Outside.L_meta_5475.no_zero C hs hr
