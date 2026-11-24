import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2407

theorem key {N M : ℕ} {I : Fin N → Fin M → Prop} {L : Set (Fin M)}
    (H : ∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5))
    {p q z : Fin N} (hpq : p ≠ q) (hq : 3 ≤ {l : Fin M | l ∈ L ∧ I q l}.ncard)
    (hz : L ⊆ {l2 : Fin M | I p l2 ∨ I z l2}) : z = q := by
  by_contra hzq
  have h3 : 2 < {l : Fin M | l ∈ L ∧ I q l}.ncard := by omega
  rw [Set.two_lt_ncard_iff] at h3
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := h3
  simp only [Set.mem_setOf_eq] at ha hb hc
  obtain ⟨haL, qa⟩ := ha
  obtain ⟨hbL, qb⟩ := hb
  obtain ⟨hcL, qc⟩ := hc
  have ha' : I p a ∨ I z a := hz haL
  have hb' : I p b ∨ I z b := hz hbL
  have hc' : I p c ∨ I z c := hz hcL
  rcases ha' with h1 | h1 <;> rcases hb' with h2 | h2 <;> rcases hc' with h3 | h3 <;>
  first
  | exact H p q a b hpq hab ⟨h1, qa, h2, qb⟩
  | exact H p q a c hpq hac ⟨h1, qa, h3, qc⟩
  | exact H p q b c hpq hbc ⟨h2, qb, h3, qc⟩
  | exact H z q a b hzq hab ⟨h1, qa, h2, qb⟩
  | exact H z q a c hzq hac ⟨h1, qa, h3, qc⟩
  | exact H z q b c hzq hbc ⟨h2, qb, h3, qc⟩

end PEqualNP.Outside.L_meta_2407

theorem PEqualNP.Outside.L_meta_2407 : ∀ (N M : ℕ) (I : Fin N → Fin M → Prop) (L : Set (Fin M)), (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → {p : Fin N | 3 ≤ {l : Fin M | l ∈ L ∧ I p l}.ncard ∧ ∃ z : Fin N, L ⊆ {l2 : Fin M | I p l2 ∨ I z l2}}.ncard ≤ 2 := by
  intro N M I L H
  by_contra hcon
  push_neg at hcon
  rw [Set.two_lt_ncard_iff] at hcon
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hcon
  simp only [Set.mem_setOf_eq] at ha hb hc
  obtain ⟨-, z, hz⟩ := ha
  have e1 : z = b := PEqualNP.Outside.L_meta_2407.key H hab hb.1 hz
  have e2 : z = c := PEqualNP.Outside.L_meta_2407.key H hac hc.1 hz
  exact hbc (e1.symm.trans e2)
