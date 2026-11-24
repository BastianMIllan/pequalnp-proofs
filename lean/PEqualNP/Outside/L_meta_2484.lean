import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2484 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → (∀ pl ∈ A, (∃ j_1 a_1 b_1, (j_1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [a_1, b_1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_1).inputs = [b_1, a_1])) ∧ {a_2 | PEqualNP.CleanedNonEdge.wireVal n C (a_1) (fun k_1 : Fin n => decide (k_1.val = pw a_2)) = true} = {pl.1} ∧ {a_3 | PEqualNP.CleanedNonEdge.wireVal n C (b_1) (fun k_2 : Fin n => decide (k_2.val = lw a_3)) = true} = {pl.2})) → A.card ≤ 2 * {j_2 : ℕ | j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  classical
  intro n N M pw lw C A _ hA
  let S : Finset ℕ := (Finset.range C.gates.length).filter
    (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and)
  have hcard : {j_2 : ℕ | j_2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j_2).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard = S.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext j
    simp [S]
  rw [hcard]
  let r : Fin N × Fin M → ℕ × Bool → Prop := fun pl jo => ∃ a b,
    ((jo.2 = true ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo.1).inputs = [a, b]) ∨
      (jo.2 = false ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo.1).inputs = [b, a])) ∧
    {x | PEqualNP.CleanedNonEdge.wireVal n C a (fun k : Fin n => decide (k.val = pw x)) = true} = {pl.1} ∧
    {x | PEqualNP.CleanedNonEdge.wireVal n C b (fun k : Fin n => decide (k.val = lw x)) = true} = {pl.2}
  have h := Finset.card_le_card_of_forall_subsingleton r (s := A)
    (t := S ×ˢ (Finset.univ : Finset Bool)) ?_ ?_
  · rw [Finset.card_product, Finset.card_univ, Fintype.card_bool] at h
    omega
  · intro pl hpl
    obtain ⟨j, a, b, ⟨hj, hop, hin⟩, h1, h2⟩ := hA pl hpl
    rcases hin with hin | hin
    · exact ⟨(j, true), by simp [S, hj, hop], a, b, Or.inl ⟨rfl, hin⟩, h1, h2⟩
    · exact ⟨(j, false), by simp [S, hj, hop], a, b, Or.inr ⟨rfl, hin⟩, h1, h2⟩
  · rintro ⟨j, o⟩ _ pl hpl pl' hpl'
    change _ ∧ r pl (j, o) at hpl
    change _ ∧ r pl' (j, o) at hpl'
    obtain ⟨_, a, b, hin, h1, h2⟩ := hpl
    obtain ⟨_, a', b', hin', h1', h2'⟩ := hpl'
    have key : a = a' ∧ b = b' := by
      rcases hin with ⟨ho, hi⟩ | ⟨ho, hi⟩ <;> rcases hin' with ⟨ho', hi'⟩ | ⟨ho', hi'⟩
      · rw [hi] at hi'
        simpa using hi'
      · simp only at ho ho'
        rw [ho] at ho'
        exact absurd ho' (by decide)
      · simp only at ho ho'
        rw [ho] at ho'
        exact absurd ho' (by decide)
      · rw [hi] at hi'
        simp only [List.cons.injEq, and_true] at hi'
        exact ⟨hi'.2, hi'.1⟩
    obtain ⟨rfl, rfl⟩ := key
    have e1 : pl.1 = pl'.1 := Set.singleton_eq_singleton_iff.mp (h1.symm.trans h1')
    have e2 : pl.2 = pl'.2 := Set.singleton_eq_singleton_iff.mp (h2.symm.trans h2')
    exact Prod.ext e1 e2
