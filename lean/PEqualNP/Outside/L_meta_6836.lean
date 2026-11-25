import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6836

theorem sub7 : ∀ v : Fin 11, v ∉ ({3, 8, 9, 10} : Finset (Fin 11)) →
    v ∈ ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)) := by decide

theorem sum3 (f : Fin 11 × Fin 11 → ℕ) :
    ∑ i ∈ ({(1, 4), (2, 5), (6, 7)} : Finset (Fin 11 × Fin 11)), f i = f (1, 4) + f (2, 5) + f (6, 7) := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  omega

end PEqualNP.Outside.L_meta_6836

theorem PEqualNP.Outside.L_meta_6836 : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : Finset (Sym2 (Fin (11 : ℕ)))),   have x4 : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};   have x5 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};   (∀ x6 ∈ x5, x1.Adj x6.1 x6.2) →     let x7 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x3;     have x8 : Finset (Fin (11 : ℕ)) := {x8 ∈ Finset.univ \ x4 | ∃ x9 ∈ x4, x7.Adj x9 x8};     let x9 : Fin (11 : ℕ) → Prop := fun (x9 : Fin (11 : ℕ)) => ∀ x10 ∈ x4, x1.Adj x10 x9 → s(x10, x9) ∈ x3;     (x8.card + {x10 ∈ x5 | x7.Adj x10.1 x10.2 ∧ x10.1 ∉ x8 ∧ x10.2 ∉ x8}.card + if x9 (0 : Fin (11 : ℕ)) then (1 : ℕ) else (0 : ℕ)) + {x10 ∈ x5 | x9 x10.1 ∨ x9 x10.2}.card + {x10 ∈ x5 | x9 x10.1 ∧ x9 x10.2 ∧ s(x10.1, x10.2) ∈ x3}.card = (7 : ℕ) := by
  intro x1 x2 x3 x4 x5 h x7 x8 x9
  have hadj : ∀ a b : Fin 11, x7.Adj a b ↔ x1.Adj a b ∧ s(a, b) ∉ x3 := by
    intro a b
    simp only [x7, SimpleGraph.deleteEdges_adj, Finset.mem_coe]
  have hx9 : ∀ v, v ∉ x4 → (x9 v ↔ v ∉ x8) := by
    intro v hv
    simp only [x9, x8, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, hv,
      not_false_eq_true, hadj, not_exists, not_and, not_not]
  have hx8 : x8 = ({0, 1, 2, 4, 5, 6, 7} : Finset (Fin 11)).filter (fun v => v ∈ x8) := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · intro hv
      exact ⟨PEqualNP.Outside.L_meta_6836.sub7 v (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2, hv⟩
    · intro hv
      exact hv.2
  have hcard : x8.card = (if (0 : Fin 11) ∈ x8 then 1 else 0) + ((if (1 : Fin 11) ∈ x8 then 1 else 0) +
      ((if (2 : Fin 11) ∈ x8 then 1 else 0) + ((if (4 : Fin 11) ∈ x8 then 1 else 0) +
      ((if (5 : Fin 11) ∈ x8 then 1 else 0) + ((if (6 : Fin 11) ∈ x8 then 1 else 0) +
      (if (7 : Fin 11) ∈ x8 then 1 else 0)))))) := by
    conv_lhs => rw [hx8]
    rw [Finset.card_filter]
    rfl
  have h14 : x1.Adj 1 4 := h (1, 4) (by simp [x5])
  have h25 : x1.Adj 2 5 := h (2, 5) (by simp [x5])
  have h67 : x1.Adj 6 7 := h (6, 7) (by simp [x5])
  have q0 := hx9 0 (by decide)
  have q1 := hx9 1 (by decide)
  have q2 := hx9 2 (by decide)
  have q4 := hx9 4 (by decide)
  have q5 := hx9 5 (by decide)
  have q6 := hx9 6 (by decide)
  have q7 := hx9 7 (by decide)
  rw [hcard]
  simp only [Finset.card_filter, x5, PEqualNP.Outside.L_meta_6836.sum3, q0, q1, q2, q4, q5, q6, q7, hadj,
    h14, h25, h67, true_and]
  have A0 : (if (0 : Fin 11) ∈ x8 then 1 else 0) + (if (0 : Fin 11) ∉ x8 then 1 else 0) = 1 := by
    by_cases a : (0 : Fin 11) ∈ x8 <;> simp [a]
  have B1 : (if (1 : Fin 11) ∈ x8 then 1 else 0) + (if (4 : Fin 11) ∈ x8 then 1 else 0) +
      (if s((1 : Fin 11), 4) ∉ x3 ∧ (1 : Fin 11) ∉ x8 ∧ (4 : Fin 11) ∉ x8 then 1 else 0) +
      (if (1 : Fin 11) ∉ x8 ∨ (4 : Fin 11) ∉ x8 then 1 else 0) +
      (if (1 : Fin 11) ∉ x8 ∧ (4 : Fin 11) ∉ x8 ∧ s((1 : Fin 11), 4) ∈ x3 then 1 else 0) = 2 := by
    by_cases a : (1 : Fin 11) ∈ x8 <;> by_cases b : (4 : Fin 11) ∈ x8 <;>
      by_cases e : s((1 : Fin 11), 4) ∈ x3 <;> simp [a, b, e]
  have B2 : (if (2 : Fin 11) ∈ x8 then 1 else 0) + (if (5 : Fin 11) ∈ x8 then 1 else 0) +
      (if s((2 : Fin 11), 5) ∉ x3 ∧ (2 : Fin 11) ∉ x8 ∧ (5 : Fin 11) ∉ x8 then 1 else 0) +
      (if (2 : Fin 11) ∉ x8 ∨ (5 : Fin 11) ∉ x8 then 1 else 0) +
      (if (2 : Fin 11) ∉ x8 ∧ (5 : Fin 11) ∉ x8 ∧ s((2 : Fin 11), 5) ∈ x3 then 1 else 0) = 2 := by
    by_cases a : (2 : Fin 11) ∈ x8 <;> by_cases b : (5 : Fin 11) ∈ x8 <;>
      by_cases e : s((2 : Fin 11), 5) ∈ x3 <;> simp [a, b, e]
  have B3 : (if (6 : Fin 11) ∈ x8 then 1 else 0) + (if (7 : Fin 11) ∈ x8 then 1 else 0) +
      (if s((6 : Fin 11), 7) ∉ x3 ∧ (6 : Fin 11) ∉ x8 ∧ (7 : Fin 11) ∉ x8 then 1 else 0) +
      (if (6 : Fin 11) ∉ x8 ∨ (7 : Fin 11) ∉ x8 then 1 else 0) +
      (if (6 : Fin 11) ∉ x8 ∧ (7 : Fin 11) ∉ x8 ∧ s((6 : Fin 11), 7) ∈ x3 then 1 else 0) = 2 := by
    by_cases a : (6 : Fin 11) ∈ x8 <;> by_cases b : (7 : Fin 11) ∈ x8 <;>
      by_cases e : s((6 : Fin 11), 7) ∈ x3 <;> simp [a, b, e]
  omega
