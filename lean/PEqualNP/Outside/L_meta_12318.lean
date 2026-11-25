import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12318

theorem polyExp (q : Polynomial ℕ) : ∃ N, ∀ j, N ≤ j → q.eval j ≤ 2 ^ j := by
  have hb : ∀ j, 1 ≤ j → q.eval j ≤ q.eval 1 * j ^ q.natDegree := by
    intro j hj
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    rw [one_pow, mul_one]
    have hi' : i < q.natDegree + 1 := Finset.mem_range.1 hi
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hj (by omega))
  have ho := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) q.natDegree
    (one_lt_two : (1 : ℝ) < 2)).const_mul_left ((q.eval 1 : ℕ) : ℝ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (ho.bound one_pos)
  refine ⟨N + 1, fun j hj => ?_⟩
  have h1 := hN j (by omega)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul] at h1
  have h2 : ((q.eval 1 * j ^ q.natDegree : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    push_cast
    exact h1
  exact le_trans (hb j (by omega)) (by exact_mod_cast h2)

theorem memL (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (k : ℕ) (x : List Bool)
    (hx : x.length = k + k) :
    x ∈ {x : List Bool | Even x.length ∧ PEqualNP.Represents.adjFun (k := x.length / 2)
      (l := x.length / 2) (A (x.length / 2)) (fun i => x.getD i false) = true} ↔
    PEqualNP.Represents.adjFun (A k) (fun i : Fin (k + k) => x.getD i false) = true := by
  have he : Even x.length := ⟨k, hx⟩
  have h2 : x.length / 2 = k := by omega
  subst h2
  simp only [Set.mem_setOf_eq]
  exact ⟨fun h => h.2, fun h => ⟨he, h⟩⟩

end PEqualNP.Outside.L_meta_12318

theorem PEqualNP.Outside.L_meta_12318 : (∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), PEqualNP.MetaComplexity.HasCircuitSize (k + l) (PEqualNP.Represents.adjFun A) s → PEqualNP.Represents.RepSizeAtMost A (2 * s + 2 * 2 ^ k + k * 2 ^ ((k + 1) / 2) + 2 * 2 ^ l + l * 2 ^ ((l + 1) / 2))) → ∀ (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (d K : ℕ), 0 < d → (∀ k, K ≤ k → ¬ PEqualNP.Represents.RepSizeAtMost (A k) (4 * 2 ^ k + 2 ^ k / d)) → {x : List Bool | Even x.length ∧ PEqualNP.Represents.adjFun (k := x.length / 2) (l := x.length / 2) (A (x.length / 2)) (fun i => x.getD i false) = true} ∈ PEqualNP.Library.NP → ¬ PEqualNP.Library.NP ⊆ PEqualNP.CircuitLowerBounds.PPoly := by
  intro hconv A d K hd hlow hNP hsub
  obtain ⟨p, hp⟩ := hsub hNP
  obtain ⟨N1, hN1⟩ := PEqualNP.Outside.L_meta_12318.polyExp
    (Polynomial.C (2 * d) * p.comp (Polynomial.C 4 * Polynomial.X))
  obtain ⟨N2, hN2⟩ := PEqualNP.Outside.L_meta_12318.polyExp
    (Polynomial.C (4 * d) * Polynomial.X + 1)
  set j := N1 + N2 + K + 1 with hj
  have ha : 2 * d * p.eval (4 * j) ≤ 2 ^ j := by
    have := hN1 j (by omega)
    simpa [Polynomial.eval_mul, Polynomial.eval_comp, mul_assoc] using this
  have hb : 4 * d * j + 1 ≤ 2 ^ j := by
    have := hN2 j (by omega)
    simpa using this
  set k := 2 * j with hk
  clear_value k j
  have hcs : PEqualNP.MetaComplexity.HasCircuitSize (k + k) (PEqualNP.Represents.adjFun (A k))
      (p.eval ((k + k : ℕ) : ℕ)) := by
    obtain ⟨C, hC1, hC2, hC3⟩ := hp (k + k)
    refine ⟨C, hC1, hC2, fun y => ?_⟩
    have e1 := hC3 (List.ofFn y) (by simp)
    have e2 := PEqualNP.Outside.L_meta_12318.memL A k (List.ofFn y) (by simp)
    have e3 : (fun i : Fin (k + k) => (List.ofFn y).getD i false) = y := by
      funext i
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp
    rw [e3] at e2
    exact Bool.eq_iff_iff.mpr (e1.trans e2)
  obtain ⟨C, h1, h2, h3⟩ := hconv k k _ (A k) hcs
  apply hlow k (by omega)
  refine ⟨C, h1, le_trans h2 ?_, h3⟩
  have hkk : k + k = 4 * j := by omega
  have hk1 : (k + 1) / 2 = j := by omega
  have hpow : (2 : ℕ) ^ k = 2 ^ j * 2 ^ j := by rw [hk, two_mul, pow_add]
  rw [hkk, hk1, hpow]
  have hdiv : 2 * p.eval (4 * j) + 2 * k * 2 ^ j ≤ 2 ^ j * 2 ^ j / d := by
    rw [Nat.le_div_iff_mul_le hd]
    have hm := Nat.mul_le_mul_right (2 ^ j) hb
    rw [hk]
    nlinarith [hm, ha]
  nlinarith [hdiv]

