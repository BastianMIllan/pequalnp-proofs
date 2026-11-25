import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8287

theorem key (n : ℕ) (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hdeg : ∀ v ∉ S, (G.neighborSet v).ncard = 3)
    (hS : ∀ u w : Fin n, G.Adj u w → u ∉ S)
    (C : Finset (Fin n)) (hC : ∀ u w : Fin n, G.Adj u w → u ∈ C ∨ w ∈ C) :
    (Finset.univ \ S).card ≤ 2 * C.card := by
  classical
  let d : Fin n → ℕ := fun v => (Finset.univ.filter (fun w => G.Adj v w)).card
  have hd3 : ∀ v ∉ S, d v = 3 := by
    intro v hv
    rw [← hdeg v hv]
    have e : G.neighborSet v = ↑(Finset.univ.filter (fun w => G.Adj v w)) := by
      ext w
      simp [SimpleGraph.mem_neighborSet]
    rw [e, Set.ncard_coe_finset]
  have hd0 : ∀ v ∈ S, d v = 0 := by
    intro v hv
    simp only [d, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w _ h
    exact hS v w h hv
  have hle : ∀ v, d v ≤ 3 := by
    intro v
    by_cases hv : v ∈ S
    · rw [hd0 v hv]
      omega
    · rw [hd3 v hv]
  have htot : ∑ v, d v = 3 * (Finset.univ \ S).card := by
    rw [← Finset.sum_sdiff (Finset.subset_univ S)]
    rw [Finset.sum_eq_zero hd0, add_zero]
    rw [Finset.sum_congr rfl (g := fun _ => 3) (fun v hv => hd3 v (Finset.mem_sdiff.mp hv).2)]
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have h1 : ∀ v, d v ≤ (if v ∈ C then d v else 0) +
      (Finset.univ.filter (fun w => G.Adj v w ∧ w ∈ C)).card := by
    intro v
    by_cases hv : v ∈ C
    · simp [hv]
    · simp only [hv, if_false, zero_add, d]
      apply Finset.card_le_card
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact ⟨hw, (hC v w hw).resolve_left hv⟩
  have h2 : ∀ w, ∑ v, (if (G.Adj v w ∧ w ∈ C) then 1 else 0) = if w ∈ C then d w else 0 := by
    intro w
    by_cases hw : w ∈ C
    · rw [if_pos hw]
      simp only [d, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : G.Adj v w
      · have h' : G.Adj w v := G.adj_symm h
        rw [if_pos ⟨h, hw⟩, if_pos h']
      · have h' : ¬ G.Adj w v := fun k => h (G.adj_symm k)
        rw [if_neg (fun k => h k.1), if_neg h']
    · rw [if_neg hw]
      apply Finset.sum_eq_zero
      intro v _
      rw [if_neg (fun k => hw k.2)]
  have h3 : ∑ v, (Finset.univ.filter (fun w => G.Adj v w ∧ w ∈ C)).card = ∑ v ∈ C, d v := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun w _ => h2 w)]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hsum : ∑ v, d v ≤ 2 * ∑ v ∈ C, d v := by
    calc ∑ v, d v ≤ ∑ v, ((if v ∈ C then d v else 0) +
          (Finset.univ.filter (fun w => G.Adj v w ∧ w ∈ C)).card) :=
          Finset.sum_le_sum (fun v _ => h1 v)
      _ = ∑ v ∈ C, d v + ∑ v ∈ C, d v := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, h3]
      _ = 2 * ∑ v ∈ C, d v := by ring
  have hC3 : ∑ v ∈ C, d v ≤ 3 * C.card := by
    calc ∑ v ∈ C, d v ≤ ∑ v ∈ C, 3 := Finset.sum_le_sum (fun v _ => hle v)
      _ = 3 * C.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega

end PEqualNP.Outside.L_meta_8287

theorem PEqualNP.Outside.L_meta_8287 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)), x2.Colorable (2 : ℕ) → (∀ x5 ∉ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 x7 : Fin x1), x2.Adj x6 x7 → x6 ∉ x3) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → ∀ (x8 : Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∈ x8 ∨ x10 ∈ x8) → (Finset.univ \ x3).card / (2 : ℕ) ≤ x8.card := by
  intro n G S _ hdeg hS _ C hC
  have := PEqualNP.Outside.L_meta_8287.key n G S hdeg hS C hC
  omega
