import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8421

theorem main (S : Fin 21 → Finset (Fin 21))
    (hS : ∀ p l : Fin 21, p ∈ S l ↔ (l.val + 21 - p.val) % 21 ∈ [(0:ℕ), 5, 7, 17, 20])
    (x4 : Fin 42 → Bool)
    (hno : ¬ ∃ (a b : Fin 42), (a.val < 21 ∧ 21 ≤ b.val ∧
      (b.val + 21 - a.val) % 21 ∈ [(0:ℕ), 5, 7, 17, 20]) ∧ x4 a = true ∧ x4 b = true)
    (hmax : ∀ (f : Fin 42 → Bool), (∀ i, x4 i = true → f i = true) →
      (¬ ∃ (a b : Fin 42), (a.val < 21 ∧ 21 ≤ b.val ∧
        (b.val + 21 - a.val) % 21 ∈ [(0:ℕ), 5, 7, 17, 20]) ∧ f a = true ∧ f b = true) → f = x4) :
    ∃ X : Finset (Fin 21), PEqualNP.GenericRejection.zeroSet S (PEqualNP.HeptadCover.missLines S X) = X ∧
      List.ofFn x4 = PEqualNP.GenericRejection.incidenceInput X (PEqualNP.HeptadCover.missLines S X) := by
  classical
  let X : Finset (Fin 21) := Finset.univ.filter fun p => x4 ⟨p.val, by omega⟩ = true
  let Y : Finset (Fin 21) := Finset.univ.filter fun l => x4 ⟨21 + l.val, by omega⟩ = true
  have hpt : ∀ p : Fin 21, p ∈ X ↔ x4 ⟨p.val, by omega⟩ = true := by
    intro p; simp [X]
  have hln : ∀ l : Fin 21, l ∈ Y ↔ x4 ⟨21 + l.val, by omega⟩ = true := by
    intro l; simp [Y]
  have hsep : ∀ p l : Fin 21, p ∈ X → l ∈ Y → p ∈ S l → False := by
    intro p l hp hl hpl
    apply hno
    refine ⟨⟨p.val, by omega⟩, ⟨21 + l.val, by omega⟩, ⟨p.isLt, by simp, ?_⟩, (hpt p).1 hp, (hln l).1 hl⟩
    have h : (21 + l.val + 21 - p.val) % 21 = (l.val + 21 - p.val) % 21 := by omega
    show (21 + l.val + 21 - p.val) % 21 ∈ _
    rw [h]; exact (hS p l).1 hpl
  have hY : PEqualNP.HeptadCover.missLines S X = Y := by
    ext l
    simp only [PEqualNP.HeptadCover.missLines, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hdis
      let f : Fin 42 → Bool := fun i => x4 i || decide (i.val = 21 + l.val)
      have hf : f = x4 := by
        apply hmax
        · intro i hi; simp [f, hi]
        · rintro ⟨a, b, ⟨ha, hb, hd⟩, hfa, hfb⟩
          have hxa : x4 a = true := by
            simpa [f, show a.val ≠ 21 + l.val by omega] using hfa
          by_cases hbl : b.val = 21 + l.val
          · have hpX : (⟨a.val, ha⟩ : Fin 21) ∈ X := (hpt _).2 hxa
            have hpl : (⟨a.val, ha⟩ : Fin 21) ∈ S l := by
              rw [hS]
              have h : (b.val + 21 - a.val) % 21 = (l.val + 21 - a.val) % 21 := by omega
              show (l.val + 21 - a.val) % 21 ∈ _
              rw [← h]; exact hd
            exact Finset.disjoint_left.1 hdis hpl hpX
          · have hxb : x4 b = true := by simpa [f, hbl] using hfb
            exact hno ⟨a, b, ⟨ha, hb, hd⟩, hxa, hxb⟩
      have := congrFun hf ⟨21 + l.val, by omega⟩
      rw [hln]
      simpa [f] using this.symm
    · intro hl
      rw [Finset.disjoint_left]
      intro p hpl hpX
      exact hsep p l hpX hl hpl
  have hX : PEqualNP.GenericRejection.zeroSet S Y = X := by
    ext p
    simp only [PEqualNP.GenericRejection.zeroSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hall
      let f : Fin 42 → Bool := fun i => x4 i || decide (i.val = p.val)
      have hf : f = x4 := by
        apply hmax
        · intro i hi; simp [f, hi]
        · rintro ⟨a, b, ⟨ha, hb, hd⟩, hfa, hfb⟩
          have hxb : x4 b = true := by
            simpa [f, show b.val ≠ p.val by omega] using hfb
          have hlY : (⟨b.val - 21, by omega⟩ : Fin 21) ∈ Y := by
            refine (hln _).2 ?_
            have e : (⟨21 + (b.val - 21), by omega⟩ : Fin 42) = b :=
              Fin.ext (show 21 + (b.val - 21) = b.val by omega)
            convert hxb
          by_cases hap : a.val = p.val
          · apply hall _ hlY
            rw [hS]
            show ((b.val - 21) + 21 - p.val) % 21 ∈ _
            have h : (b.val - 21 + 21 - p.val) % 21 = (b.val + 21 - a.val) % 21 := by omega
            rw [h]; exact hd
          · have hxa : x4 a = true := by simpa [f, hap] using hfa
            exact hno ⟨a, b, ⟨ha, hb, hd⟩, hxa, hxb⟩
      have := congrFun hf ⟨p.val, by omega⟩
      rw [hpt]
      simpa [f] using this.symm
    · intro hp l hl hpl
      exact hsep p l hp hl hpl
  refine ⟨X, ?_, ?_⟩
  · rw [hY, hX]
  · rw [hY]
    refine (List.ofFn_add (m := 21) (n := 21) (f := x4)).trans ?_
    unfold PEqualNP.GenericRejection.incidenceInput
    congr 1
    · congr 1
      funext i
      by_cases hi : i ∈ X
      · rw [decide_eq_true hi]; exact (hpt i).1 hi
      · rw [decide_eq_false hi]
        exact Bool.eq_false_iff.2 (fun h => hi ((hpt i).2 h))
    · congr 1
      funext j
      by_cases hj : j ∈ Y
      · rw [decide_eq_true hj]; exact (hln j).1 hj
      · rw [decide_eq_false hj]
        exact Bool.eq_false_iff.2 (fun h => hj ((hln j).2 h))

end PEqualNP.Outside.L_meta_8421

theorem PEqualNP.Outside.L_meta_8421 : let x1 : Type := Fin (21 : ℕ); have x2 : x1 → Finset x1 := fun (x2 : x1) => {x3 : x1 | (↑x2 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]}; have x3 : (Fin (42 : ℕ) → Bool) → Prop := fun (x3 : Fin (42 : ℕ) → Bool) => ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true; ∀ (x4 : Fin (42 : ℕ) → Bool),   ¬x3 x4 →     (∀ (x6 : Fin (42 : ℕ) → Bool), (∀ (x7 : Fin (42 : ℕ)), x4 x7 = Bool.true → x6 x7 = Bool.true) → ¬x3 x6 → x6 = x4) →       ∃ (x7 : Finset x1),         have x8 : Finset (Fin (21 : ℕ)) := PEqualNP.HeptadCover.missLines x2 x7;         PEqualNP.GenericRejection.zeroSet x2 x8 = x7 ∧ List.ofFn x4 = PEqualNP.GenericRejection.incidenceInput x7 x8 := by
  dsimp only
  intro x4 hno hmax
  exact PEqualNP.Outside.L_meta_8421.main _ (fun p l => by simp) x4 hno hmax
