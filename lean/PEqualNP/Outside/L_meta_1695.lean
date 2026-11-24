import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1695 : (∀ (n m s k : ℕ) (L : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → C.size ≤ s → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → (∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 → PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x (fun l => decide (l ∈ Y))) = true → ∃ j ∈ Y, ∃ p ∈ L j, x p = true) → (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true)).card ≤ (6 * k + 6) * s + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k) → ∀ (n m k : ℕ) (L : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C → Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 ∧ ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, 0 < (C.lineDegrees (n + m) (Finset.Ico n (n + m))).getD i 0} ≤ k → (∀ (x : Fin n → Bool) (y : Fin m → Bool), PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append x y) = decide (∃ j : Fin m, ∃ p ∈ L j, x p = true ∧ y j = true)) → (∑ j : Fin m, (L j).card) ≤ (6 * k + 6) * C.size + (12 * k ^ 2 + 13 * k + 2) * m + 6 * k ^ 2 + 5 * k := by
  intro H n m k L C hL hM hR hk hf
  have hcond : ∀ (p : Fin n) (j : Fin m), p ∈ L j →
      PEqualNP.MetaComplexity.circuitFun (n + m) C
        (Fin.append (fun i => decide (i = p)) (fun l => decide (l = j))) = true := by
    intro p j hp
    rw [hf (fun i => decide (i = p)) (fun l => decide (l = j)), decide_eq_true_eq]
    exact ⟨j, p, hp, by simp, by simp⟩
  have hsound : ∀ (x : Fin n → Bool) (Y : Finset (Fin m)), Y.card ≤ 1 →
      PEqualNP.MetaComplexity.circuitFun (n + m) C
        (Fin.append x (fun l => decide (l ∈ Y))) = true → ∃ j ∈ Y, ∃ p ∈ L j, x p = true := by
    intro x Y _ hT
    rw [hf x (fun l => decide (l ∈ Y)), decide_eq_true_eq] at hT
    obtain ⟨j, p, hp, hx, hy⟩ := hT
    exact ⟨j, by simpa using hy, p, hp, hx⟩
  have hmain := H n m C.size k L C hL hM hR le_rfl hk hsound
  have hsum : (∑ j : Fin m, (L j).card) = (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ L e.2 ∧ PEqualNP.MetaComplexity.circuitFun (n + m) C (Fin.append (fun i => decide (i = e.1)) (fun l => decide (l = e.2))) = true)).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.card_filter]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h, hcond p j h⟩, fun h => h.1⟩
  rw [hsum]
  exact hmain
