import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2411

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

open Classical in
lemma ncard_eq (C : Circuit) :
    {ja : ℕ | ja < C.gates.length ∧ (gateAt C ja).op = GateOp.and}.ncard
      = ((Finset.range C.gates.length).filter (fun ja => (gateAt C ja).op = GateOp.and)).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext ja
  simp

end PEqualNP.Outside.L_meta_2411

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_2411 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → (∀ e ∈ A, ∃ (j a b : ℕ), (j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) = a ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = b) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) = b ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = a))) ∧ {x1 : Fin N | R (pw x1) a} = {e.1} ∧ {y1 : Fin M | R (lw y1) b} = {e.2}) → A.card ≤ 2 * {ja : ℕ | ja < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C ja).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  classical
  intro n N M pw lw C A _ R _ hA
  rw [PEqualNP.Outside.L_meta_2411.ncard_eq]
  set S := (Finset.range C.gates.length).filter (fun ja => (gateAt C ja).op = GateOp.and) with hS
  have key : ∀ e : Fin N × Fin M, ∃ p : ℕ × Bool, e ∈ A → p.1 ∈ S ∧
      ∃ a b : ℕ, (if p.2 = true then ((gateAt C p.1).inputs.getD 0 0 = a ∧ (gateAt C p.1).inputs.getD 1 0 = b)
        else ((gateAt C p.1).inputs.getD 0 0 = b ∧ (gateAt C p.1).inputs.getD 1 0 = a)) ∧
        {x1 : Fin N | R (pw x1) a} = {e.1} ∧ {y1 : Fin M | R (lw y1) b} = {e.2} := by
    intro e
    by_cases he : e ∈ A
    · obtain ⟨j, a, b, ⟨hj, hand, hor⟩, h1, h2⟩ := hA e he
      rcases hor with h | h
      · exact ⟨(j, true), fun _ => ⟨by simp [hS, hj, hand], a, b, by simpa using h, h1, h2⟩⟩
      · exact ⟨(j, false), fun _ => ⟨by simp [hS, hj, hand], a, b, by simpa using h, h1, h2⟩⟩
    · exact ⟨(0, true), fun h => absurd h he⟩
  choose f hf using key
  have hmaps : ∀ e ∈ A, f e ∈ S ×ˢ (Finset.univ : Finset Bool) := by
    intro e he
    simpa using (hf e he).1
  have hinj : Set.InjOn f A := by
    intro e he e' he' heq
    obtain ⟨_, a, b, hab, h1, h2⟩ := hf e he
    obtain ⟨_, a', b', hab', h1', h2'⟩ := hf e' he'
    rw [heq] at hab
    have hA' : a = a' ∧ b = b' := by
      cases hb : (f e').2
      · simp only [hb, Bool.false_eq_true, ite_false] at hab hab'
        omega
      · simp only [hb, ite_true] at hab hab'
        omega
    obtain ⟨rfl, rfl⟩ := hA'
    rw [h1] at h1'
    rw [h2] at h2'
    exact Prod.ext (Set.singleton_eq_singleton_iff.mp h1') (Set.singleton_eq_singleton_iff.mp h2')
  calc A.card ≤ (S ×ˢ (Finset.univ : Finset Bool)).card :=
        Finset.card_le_card_of_injOn f (fun e he => hmaps e he) hinj
    _ = 2 * S.card := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm]
