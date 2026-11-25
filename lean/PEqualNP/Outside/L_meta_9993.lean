import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9993

def A (i j : Fin 9) : Bool := (([252, 504, 497, 483, 455, 399, 287, 63, 126] : List ℕ).getD i.val 0).testBit j.val

def RM : List ℕ := [1, 34, 28, 263, 136, 112, 448]

def CM : List ℕ := [252, 392, 449, 112, 35, 263, 30]

def RR (k : ℕ) : Finset (Fin 9) := Finset.univ.filter (fun i => (RM.getD k 0).testBit i.val = true)

def CC (k : ℕ) : Finset (Fin 9) := Finset.univ.filter (fun j => (CM.getD k 0).testBit j.val = true)

set_option maxRecDepth 100000 in
theorem hmono : ∀ k : Fin 7, ∀ i j : Fin 9, (RM.getD k.val 0).testBit i.val = true →
    (CM.getD k.val 0).testBit j.val = true → A i j = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem hcov : ∀ i j : Fin 9, A i j = true → ∃ k : Fin 7, (RM.getD k.val 0).testBit i.val = true ∧
    (CM.getD k.val 0).testBit j.val = true := by decide +kernel

theorem main_aux : ∃ L : List (Finset (Fin 9) × Finset (Fin 9)), L.length ≤ 7 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([252, 504, 497, 483, 455, 399, 287, 63, 126] : List ℕ).getD i.val 0).testBit j.val = true) ∧ ∀ (i : Fin 9) (j : Fin 9), (([252, 504, 497, 483, 455, 399, 287, 63, 126] : List ℕ).getD i.val 0).testBit j.val = true → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨(List.range 7).map (fun k => (RR k, CC k)), by simp, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
    simp only [RR, CC, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact hmono ⟨k, List.mem_range.1 hk⟩ i j hi hj
  · intro i j h
    obtain ⟨k, h1, h2⟩ := hcov i j h
    refine ⟨(RR k.val, CC k.val), List.mem_map.2 ⟨k.val, List.mem_range.2 k.isLt, rfl⟩, ?_, ?_⟩
    · simp only [RR, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h1
    · simp only [CC, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h2

end PEqualNP.Outside.L_meta_9993

theorem PEqualNP.Outside.L_meta_9993 : ∃ L : List (Finset (Fin 9) × Finset (Fin 9)), L.length ≤ 7 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([252, 504, 497, 483, 455, 399, 287, 63, 126] : List ℕ).getD i.val 0).testBit j.val = true) ∧ ∀ (i : Fin 9) (j : Fin 9), (([252, 504, 497, 483, 455, 399, 287, 63, 126] : List ℕ).getD i.val 0).testBit j.val = true → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 :=
  PEqualNP.Outside.L_meta_9993.main_aux
