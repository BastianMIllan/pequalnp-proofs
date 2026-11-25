import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7081

open PEqualNP.AndCount

-- Gate i reads, on each side, the bare variables of B i whose point set lies in that side,
-- and the earlier gates whose point set lies in that side; the output reads every gate
-- whose point set lies in the target.
abbrev circ (n k : ℕ) (P : Finset (Finset (Fin n))) (B : Fin k → Finset (Fin n))
    (L R : Fin k → Finset (Finset (Fin n))) (T : Finset (Finset (Fin n))) :
    AndCountCircuit n where
  size := k
  leftVars i := (B i).filter (fun v => P.filter (fun r => v ∈ r) ⊆ L i)
  leftGates i := Finset.univ.filter (fun j => j < i ∧ L j ∩ R j ⊆ L i)
  rightVars i := (B i).filter (fun v => P.filter (fun r => v ∈ r) ⊆ R i)
  rightGates i := Finset.univ.filter (fun j => j < i ∧ L j ∩ R j ⊆ R i)
  outVars := ∅
  outGates := Finset.univ.filter (fun j => L j ∩ R j ⊆ T)

theorem side_spec {n k : ℕ} (P : Finset (Finset (Fin n))) (Bi : Finset (Fin n))
    (G : Fin k → Finset (Finset (Fin n))) (S : Finset (Finset (Fin n))) (i : Fin k)
    (val : Fin k → Bool) (p : Finset (Fin n)) (hp : p ∈ P)
    (hval : ∀ j : Fin k, j < i → (val j = true ↔ p ∈ G j))
    (hS : ∀ q ∈ S, (∃ v ∈ Bi, q ∈ P.filter (fun r => v ∈ r) ∧ P.filter (fun r => v ∈ r) ⊆ S) ∨
      ∃ j < i, q ∈ G j ∧ G j ⊆ S) :
    AndCountCircuit.sideTrue p (Bi.filter (fun v => P.filter (fun r => v ∈ r) ⊆ S))
      (Finset.univ.filter (fun j => j < i ∧ G j ⊆ S)) i val = true ↔ p ∈ S := by
  unfold AndCountCircuit.sideTrue
  rw [decide_eq_true_iff]
  constructor
  · rintro (⟨v, hv, hvp⟩ | ⟨j, hj, hji, hvj⟩)
    · rw [Finset.mem_filter] at hv
      exact hv.2 (Finset.mem_filter.mpr ⟨hp, hvp⟩)
    · rw [Finset.mem_filter] at hj
      exact hj.2.2 ((hval j hji).mp hvj)
  · intro hpS
    rcases hS p hpS with ⟨v, hv, hpv, hsub⟩ | ⟨j, hji, hpj, hsub⟩
    · exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨hv, hsub⟩, (Finset.mem_filter.mp hpv).2⟩
    · exact Or.inr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji, hsub⟩, hji,
        (hval j hji).mpr hpj⟩

theorem gate_spec {n k : ℕ} (P : Finset (Finset (Fin n))) (B : Fin k → Finset (Fin n))
    (L R : Fin k → Finset (Finset (Fin n))) (T : Finset (Finset (Fin n)))
    (hLR : ∀ i : Fin k,
      (∀ q ∈ L i, (∃ v ∈ B i, q ∈ P.filter (fun r => v ∈ r) ∧ P.filter (fun r => v ∈ r) ⊆ L i) ∨
        ∃ j < i, q ∈ L j ∩ R j ∧ L j ∩ R j ⊆ L i) ∧
      (∀ q ∈ R i, (∃ v ∈ B i, q ∈ P.filter (fun r => v ∈ r) ∧ P.filter (fun r => v ∈ r) ⊆ R i) ∨
        ∃ j < i, q ∈ L j ∩ R j ∧ L j ∩ R j ⊆ R i))
    (p : Finset (Fin n)) (hp : p ∈ P) :
    ∀ d : ℕ, ∀ i : Fin k, i.val < d →
      ((circ n k P B L R T).gateValFuel p d i = true ↔ p ∈ L i ∩ R i) := by
  intro d
  induction d with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ d ih =>
    intro i hi
    have hval : ∀ j : Fin k, j < i →
        ((circ n k P B L R T).gateValFuel p d j = true ↔ p ∈ L j ∩ R j) :=
      fun j hj => ih j (by have := Fin.lt_def.mp hj; omega)
    have h1 := side_spec P (B i) (fun j => L j ∩ R j) (L i) i
      ((circ n k P B L R T).gateValFuel p d) p hp hval (hLR i).1
    have h2 := side_spec P (B i) (fun j => L j ∩ R j) (R i) i
      ((circ n k P B L R T).gateValFuel p d) p hp hval (hLR i).2
    show (AndCountCircuit.sideTrue p ((B i).filter (fun v => P.filter (fun r => v ∈ r) ⊆ L i))
        (Finset.univ.filter (fun j => j < i ∧ L j ∩ R j ⊆ L i)) i
        ((circ n k P B L R T).gateValFuel p d) &&
      AndCountCircuit.sideTrue p ((B i).filter (fun v => P.filter (fun r => v ∈ r) ⊆ R i))
        (Finset.univ.filter (fun j => j < i ∧ L j ∩ R j ⊆ R i)) i
        ((circ n k P B L R T).gateValFuel p d)) = true ↔ p ∈ L i ∩ R i
    rw [Bool.and_eq_true, Finset.mem_inter]
    exact and_congr h1 h2

theorem eval_spec {n k : ℕ} (P : Finset (Finset (Fin n))) (B : Fin k → Finset (Fin n))
    (L R : Fin k → Finset (Finset (Fin n))) (T : Finset (Finset (Fin n)))
    (hLR : ∀ i : Fin k,
      (∀ q ∈ L i, (∃ v ∈ B i, q ∈ P.filter (fun r => v ∈ r) ∧ P.filter (fun r => v ∈ r) ⊆ L i) ∨
        ∃ j < i, q ∈ L j ∩ R j ∧ L j ∩ R j ⊆ L i) ∧
      (∀ q ∈ R i, (∃ v ∈ B i, q ∈ P.filter (fun r => v ∈ r) ∧ P.filter (fun r => v ∈ r) ⊆ R i) ∨
        ∃ j < i, q ∈ L j ∩ R j ∧ L j ∩ R j ⊆ R i))
    (hT : ∀ q ∈ T, ∃ j : Fin k, q ∈ L j ∩ R j ∧ L j ∩ R j ⊆ T) :
    ∀ p ∈ P, (circ n k P B L R T).eval p = true ↔ p ∈ T := by
  intro p hp
  have hg : ∀ j : Fin k, (circ n k P B L R T).gateVal p j = true ↔ p ∈ L j ∩ R j :=
    fun j => gate_spec P B L R T hLR p hp k j j.isLt
  unfold AndCountCircuit.eval
  rw [decide_eq_true_iff]
  constructor
  · rintro (⟨v, hv, _⟩ | ⟨j, hj, hgj⟩)
    · exact absurd hv (by simp)
    · exact (Finset.mem_filter.mp hj).2 ((hg j).mp hgj)
  · intro hpT
    obtain ⟨j, hpj, hsub⟩ := hT p hpT
    exact Or.inr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub⟩, (hg j).mpr hpj⟩

theorem count_spec {n k : ℕ} (P : Finset (Finset (Fin n))) (B : Fin k → Finset (Fin n))
    (L R : Fin k → Finset (Finset (Fin n))) (T : Finset (Finset (Fin n))) (v : Fin n) :
    (Finset.univ.filter (fun i : Fin k => v ∈ (circ n k P B L R T).leftVars i ∨
      v ∈ (circ n k P B L R T).rightVars i)).card ≤
      (Finset.univ.filter (fun i : Fin k => v ∈ B i)).card := by
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases hi.2 with h | h
  · exact (Finset.mem_filter.mp h).1
  · exact (Finset.mem_filter.mp h).1

theorem wf_spec {n k : ℕ} (P : Finset (Finset (Fin n))) (B : Fin k → Finset (Fin n))
    (L R : Fin k → Finset (Finset (Fin n))) (T : Finset (Finset (Fin n))) :
    (circ n k P B L R T).WellFormed := by
  intro i
  exact ⟨fun j hj => (Finset.mem_filter.mp hj).2.1, fun j hj => (Finset.mem_filter.mp hj).2.1⟩

end PEqualNP.Outside.L_meta_7081

theorem PEqualNP.Outside.L_meta_7081 : ∀ (x1 x2 : ℕ),   let x3 : Type := Finset (Finset (Fin x1));   have x4 : Finset (Fin x2) := Finset.univ;   ∀ (x5 : x3) (x6 : Fin x2 → Finset (Fin x1)) (x7 x8 : Fin x2 → x3) (x9 : x3),     have x10 : Fin x1 → Finset (Finset (Fin x1)) := fun (x10 : Fin x1) => {x11 ∈ x5 | x10 ∈ x11};     have x11 : Fin x2 → x3 := fun (x11 : Fin x2) => x7 x11 ∩ x8 x11;     have x12 : Fin x2 → x3 → Prop := fun (x12 : Fin x2) (x13 : x3) => ∀ x14 ∈ x13, (∃ x16 ∈ x6 x12, x14 ∈ x10 x16 ∧ x10 x16 ⊆ x13) ∨ ∃ x16 < x12, x14 ∈ x11 x16 ∧ x11 x16 ⊆ x13;     (∀ (x13 : Fin x2), x12 x13 (x7 x13) ∧ x12 x13 (x8 x13)) →       (∀ x14 ∈ x9, ∃ (x16 : Fin x2), x14 ∈ x11 x16 ∧ x11 x16 ⊆ x9) →         ∃ (x15 : PEqualNP.AndCount.AndCountCircuit x1),           x15.WellFormed ∧             x15.size = x2 ∧               (have x16 : Finset (Fin x15.size) := Finset.univ;                 ∀ (x17 : Fin x1), {x18 ∈ x16 | x17 ∈ x15.leftVars x18 ∨ x17 ∈ x15.rightVars x18}.card ≤ {x18 ∈ x4 | x17 ∈ x6 x18}.card) ∧                 ∀ x16 ∈ x5, x15.eval x16 = Bool.true ↔ x16 ∈ x9 := by
  intro n k
  dsimp only
  intro P B L R T
  intro hLR hT
  exact ⟨PEqualNP.Outside.L_meta_7081.circ n k P B L R T,
    PEqualNP.Outside.L_meta_7081.wf_spec P B L R T, rfl,
    fun v => PEqualNP.Outside.L_meta_7081.count_spec P B L R T v,
    PEqualNP.Outside.L_meta_7081.eval_spec P B L R T hLR hT⟩
